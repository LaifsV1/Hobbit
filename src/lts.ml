(* LTS USING IMMUTABLE LIST *)

open Ast                 (* Term Abstract Syntax Tree *)
open Reductions_ast
open Reductions          (* Term Semantics Reduction Rules *)
open Z3api               (* Z3 Interface to for symbolic execution *)
open Upto_tools          (* Types and Functions for Upto Techniques *)
open Normalisation
open Generalisations

(* Main types in this file:
  *
  *
  * *)

(* LTS configurations
 *
 * ** config: Single configuration
 * fields:
 * - g: the knowledge environment
 * - k: the evaluation context stack
 * - s: store
 * - e: Some CEK expression (proponent config) / None (opponent config)
 *
 * ** config_pair
 * fields:
 * - a: common set of abstract names
 * - c1: Some config (regular 1st config) / None (bottom 1st config)
 * - c2: Some config (regular 2nd config) / None (bottom 2nd config)
 * - tr: the trace that led to this config pair (last transition is first in the list)
 *
 * Invariants:
 * (c1 = None) OR (c2 = None) OR all of the following hold:
 *
 * - List.length c1.g = List.length c2.g
 * - List.length c1.k = List.length c2.k
 * - c1.e = None iff c2.e = None
 *
 * How to use the g component (knowledge environment list):
 * - New values are added at the beginning of the list.
 * - The head of the list is assumed to have index (List.length g)
 * - The last element in the list is assumed to have index 1
 *
 * *)

(** EXIT STATUS **)
let exit_eq = 43
let exit_ineq = 42
let exit_unknown = 0

(*** proponent values used for LTS labels ***)
type prvalue = PrIndex of int | PrConst of value | PrTuple of prvalue list

let rec string_of_prvalue v =
  match v with
  | PrIndex i -> Printf.sprintf "_idx_%d_" i
  | PrConst c -> string_of_val c
  | PrTuple vs ->
     let rec string_of_list ls str =
       match ls with
       | v::vs -> string_of_list vs (Printf.sprintf "%s,%s" str (string_of_prvalue v))
       | [] -> str
     in
     Printf.sprintf "(%s)" (string_of_list vs "")

(*** integer map for Gamma and functions to manipulate Gamma ***)
module StringSet = Set.Make(String)
module IntMap = Map.Make(Int)
type g_map = (value IntMap.t)

let g_empty () = IntMap.empty

let g_filter f g = IntMap.filter f g
let g_add v g =
  let new_index =
    match IntMap.max_binding_opt g with
    | Some (max_index,_) -> max_index + 1
    | None -> 1
  in
  IntMap.add new_index v g , new_index

let g_to_list g = IntMap.bindings g
let g_to_val_list g =
  let glist = IntMap.bindings g in
  let sorted_glist = List.sort (fun (k1,_) (k2,_) -> compare k1 k2) glist in
  let vallist = List.map snd sorted_glist in
  vallist
let string_of_g g =
  String.concat "," (List.map (fun (idx,v) -> Printf.sprintf "(%d,%s)" idx (string_of_val v)) (g_to_list g))

(*** integer set and type map for A ***)
(* module IntSet = Set.Make(Int) --- int set in upto_tools.ml*)
module TypeMap = Map.Make(Type)
type abs_it_map = Type.t IntMap.t
type abs_ti_map = IntSet.t TypeMap.t
type abs_set = {next:int ; it:abs_it_map ; ti:abs_ti_map} (* next id, id -> type, type -> idset *)

let abs_next_id : Type.t -> abs_set -> (int * abs_set) =
  fun t {next;it;ti} ->
  let new_next = next + 1 in
  let next = get_fresh_id () in
  let new_it = IntMap.add next t it in
  let new_ti =
    match TypeMap.find_opt t ti with
    | None -> TypeMap.add t (IntSet.singleton next) ti
    | Some iset -> TypeMap.add t (IntSet.add next iset) ti
  in
  next , {next=new_next ; it=new_it ; ti=new_ti}

let abs_remove_id : int -> abs_set -> abs_set =
  fun id ({next;it;ti} as abs) ->
  match IntMap.find_opt id it with
  | None -> abs
  | Some t ->
     let new_it = IntMap.remove id it in
     let new_ti =
       match TypeMap.find_opt t ti with
       | None -> failwith "abs_remove_id: it and ti desync"
       | Some iset -> TypeMap.add t (IntSet.remove id iset) ti
     in
     {abs with it=new_it;ti=new_ti}

let empty_abs_set = {next=0 ; it=IntMap.empty ; ti=TypeMap.empty}

(*** types used for the LTS ***)
type trans =
  | Tau
  | OpCall of prvalue * value (* gamma index * AbsCon or AbsFun or Tuple of AbsFun/AbsCon *)
  | PrCall of value * prvalue (* AbsFun * value *)
  | OpRet of value            (* AbsCon or AbsFun or Tuple of AbsFun/AbsCon *)
  | PrRet of prvalue          (* ConstVal or AbsCon or AbsFun *)
  | Markup of string          (* used in traces to mark certain points *)

type ocall = {oc_i: int; oc_gs1: (g_map * store) option; oc_gs2: (g_map * store) option}
type typed_eval_cxt = eval_cxt * Type.t
type config = {g: g_map; k: typed_eval_cxt list; s: store; e: cek_exp option}
type config_pair = {a: abs_set; c1: config option; c2: config option;
                    tr: trans list; bound: int * int; sigma: sigma * dep_tree; ocall_stack: ocall list}

(*** helper functions ***)
let string_of_trans = function
    | Tau -> "-tau->"
    | OpCall (pri, v) -> Printf.sprintf "-op_call %s %s->" (string_of_prvalue pri) (string_of_val v)
    | PrCall (v, prv) -> Printf.sprintf "-pr_call %s %s->" (string_of_val v) (string_of_prvalue prv)
    | OpRet v -> Printf.sprintf "-op_ret %s->" (string_of_val v)
    | PrRet v -> Printf.sprintf "-pr_ret %s->" (string_of_prvalue v)
    | Markup s -> Printf.sprintf "-[ %s ]->" s

let string_of_trace tr =
  List.fold_left (fun rest label -> (string_of_trans label) ^ "\n" ^ rest) "" tr

let rec string_of_k k =
  match k with
  | [] -> "[]"
  | (cxt,t)::xs ->
     (Printf.sprintf "(%s : %s)"(Reductions_ast.string_of_ecxt cxt) (Type.string_of_t t))
     ^ "::" ^ (string_of_k xs)

let string_of_s s =
  String.concat "," (List.map (fun (k,v) ->
                         Printf.sprintf "(%s |-> %s)"
                           (string_of_loc k) (string_of_val v)) (StoreMap.bindings s))

let string_of_cfg {g; k; s; e} =
  let e_str = match e with
    | None -> "."       
    | Some cek_e ->  (string_of_exp (unfocus cek_e))
  in
  Printf.sprintf "<<<===G = %s;\n===K = %s;\n===s = %s;\n===e = %s>>>"
    (string_of_g g)
    (string_of_k k)
    (string_of_s s)
    e_str

let string_of_cfg_pair {a; c1; c2; tr; bound = (bound1,bound2); sigma = (sigma,dtree)} =
  let str_of_c c =
    match c with
    | None -> "."
    | Some c -> string_of_cfg c
  in
  Printf.sprintf
    "<<a = %s;\n  tr = %s;\n  c1 = %s;\n  c2 = %s;\n  bound=%s,%s;\n sigma=%s\n dtree=%s>>"
    (string_of_int a.next)
    (string_of_trace tr)
    (str_of_c c1)
    (str_of_c c2)
    (string_of_int bound1)
    (string_of_int bound2)
    (string_of_sigma sigma)
    (string_of_dtree dtree)

(*** bound reached flag ***)
let bound_reached = ref false

(*** debug instrumentation ***)
let debug_traces = ref false
let print_debug_traces str =
  if !debug_traces  then
    Printf.printf "[traces] %s\n" str

let debug_confs = ref false
let print_debug_confs str =
  if !debug_confs  then
    Printf.printf "[configurations] %s\n" str

let debug_sigma = ref false
let print_debug_sigma str =
  if !debug_sigma  then
    Printf.printf "[symbolic-environment] %s\n" str

let debug_memo = ref false
let print_debug_memo str =
  if !debug_memo  then
    Printf.printf "[memoisation] %s\n" str

let debug_norm = ref false
let print_debug_norm str =
  if !debug_norm  then
    Printf.printf "[normalisation] %s\n" str

let debug_gc = ref false
let print_debug_gc str =
  if !debug_gc  then
    Printf.printf "[garbage-collection] %s\n" str

let debug_sep = ref false
let print_debug_sep str =
  if !debug_sep  then
    Printf.printf "[separation] %s\n" str

let debug_nr = ref false
let print_debug_nr str =
  if !debug_nr  then
    Printf.printf "[name-reuse] %s\n" str

let debug_id = ref false
let print_debug_id str =
  if !debug_id  then
    Printf.printf "[identity] %s\n" str

let debug_sigma_gc = ref false
let print_debug_sigma_gc str =
  if !debug_sigma_gc  then
    Printf.printf "[sigma-garbage-collection] %s\n" str

let debug_sigma_norm = ref false
let print_debug_sigma_norm str =
  if !debug_sigma_norm  then
    Printf.printf "[sigma-normalisation] %s\n" str

let debug_sigma_simp = ref false
let print_debug_sigma_simp str =
  if !debug_sigma_simp  then
    Printf.printf "[sigma-simplification] %s\n" str

let debug_generalise = ref false
let print_debug_generalise str =
  if !debug_generalise  then
    Printf.printf "[generalisation] %s\n" str

let debug_gamma_duplicates = ref false
let print_debug_gamma_duplicates str =
  if !debug_gamma_duplicates  then
    Printf.printf "[gamma-duplicates] %s\n" str

let debug_reentry = ref false
let print_debug_reentry str =
  if !debug_reentry  then
    Printf.printf "[reentry] %s\n" str

let lazy_print_debug f d =
  if !d  then f ()

(*****************************************************
 * GARBAGE-COLLECTION, NORMALISATION AND MEMOISATION *
 *****************************************************)
(*** memoisation ***)
let flag_memo = ref false

type minimal_cfg = {min_g: value list;
                    min_k: typed_eval_cxt list;
                    min_s: string;
                    min_e: cek_exp option}

type minimal_cfg_pair = {min_c1: minimal_cfg option;
                         min_c2: minimal_cfg option;
                         min_sigma: sigma}

let minimal_of_cfg_opt cfg_opt =
  match cfg_opt with
  | None -> None
  | Some {g; k; s; e} ->
     Some {min_g = g_to_val_list g; min_k = k; min_s = string_of_s s; min_e = e}

let minimal_of_cfg_pair {a; c1; c2; tr; bound = (bound1,bound2); sigma=(sigma,dtree)} =
  {min_c1 = minimal_of_cfg_opt c1; min_c2 = minimal_of_cfg_opt c2; min_sigma = sigma}

let init_memoisation_cache n =
  let dummy_cfg = Some {min_g = []; min_k = []; min_s = ""; min_e = None} in    
  let dummy_cfg_pair =
    {min_c1 = dummy_cfg;
     min_c2 = dummy_cfg;
     min_sigma = []}
  in
  Memoisation.make_bounded_set n dummy_cfg_pair

(*** get names ***)
let get_conf_names : config option -> int -> conf_names option =
  fun cfg nxtid ->
  match cfg with
  | None -> None
  | Some {g; k; s; e} ->
     let starting_names = {empty_conf_names with nxtid=nxtid} in
     let g_names = List.fold_right (fun (i,v) ls -> names_of_value v s ls) (g_to_list g) starting_names in
     let gk_names = List.fold_right (fun (ecxt,typ) ls -> names_of_context ecxt s ls) k g_names in
     let gke_names =
       match e with
       | None -> gk_names
       | Some cek -> names_of_cek_exp cek s gk_names
     in
     Some gke_names

(*** garbage collection ***)
let flag_gc = ref false

let garbage_collect_conf : config option -> conf_names option -> config option =
  fun cfg names ->
  match cfg , names with
  | None , None -> None
  | Some cfg , Some { nxtid ; vars ; locs ; abs } ->
     let new_s = garbage_collect cfg.s locs print_debug_gc in
     print_debug_gc (Printf.sprintf "new store: %s" (string_of_s new_s));
     Some {cfg with s = new_s}
  | Some _ , None -> failwith "lts.ml garbage collection: mismatch option of cfg and names (1)"
  | None , Some _ -> failwith "lts.ml garbage collection: mismatch option of cfg and names (2)"

(*** sigma garbage collection ***)
let flag_sigma_gc = ref false

let garbage_collect_sigma : (sigma * dep_tree) -> conf_names option -> conf_names option ->
                            (sigma * dep_tree) =
  fun (sigma,dtree) names1 names2 ->
  if not !flag_sigma_gc then sigma,dtree else
    begin
      print_debug_sigma_gc "CALLING: garbage_collect_sigma";
      match names1,names2 with
      | Some names1 , Some names2 -> Upto_tools.sigma_gc sigma dtree names1 names2
      | Some names1 , None -> Upto_tools.sigma_gc sigma dtree names1 empty_conf_names
      | None , Some names2 -> Upto_tools.sigma_gc sigma dtree names2 empty_conf_names
      | None , None -> failwith "garbage_collect_sigma: this shouldn't be called on a None-None conf pair"
    end
(*** normalisation ***)
let flag_norm = ref false

let normalise_conf : config option -> conf_names option -> name_map -> config option =
  fun cfg names sigma_names ->
  match cfg , names with
  | None , None -> None
  | Some {g; k; s; e} , Some names ->
     let new_g = IntMap.map (fun v -> normalise_val v names sigma_names) g in
     let new_k = List.map (fun (a,b) -> normalise_cxt a names sigma_names, b) k in
     let new_s = mk_normalised_store names sigma_names s in
     print_debug_gc (Printf.sprintf "NEW S: %s" (string_of_s new_s));
     let new_e =
       match e with
       | None -> None
       | Some e -> Some (normalise_cek_exp e names sigma_names)
     in
     Some {g = new_g; k = new_k; s = new_s; e = new_e}
  | Some _ , None -> failwith "lts.ml garbage collection: mismatch option of cfg and names (1)"
  | None , Some _ -> failwith "lts.ml garbage collection: mismatch option of cfg and names (2)"

(*** sigma normalisation ***)
let flag_sigma_norm = ref false

(*** sigma simplification ***)
let flag_sigma_simp = ref false
let simplify_sigma : (sigma * dep_tree) -> conf_names option -> conf_names option ->
                            (sigma * dep_tree) =
  fun sigma names1 names2 ->
  if not !flag_sigma_simp then sigma else
    begin
      print_debug_sigma_simp "CALLING: simplify_sigma";
      match names1,names2 with
      | Some names1 , Some names2 -> Upto_tools.sigma_simp sigma names1 names2
      | Some names1 , None -> Upto_tools.sigma_simp sigma names1 empty_conf_names
      | None , Some names2 -> Upto_tools.sigma_simp sigma names2 empty_conf_names
      | None , None -> failwith "simplify_sigma: this shouldn't be called on a None-None conf pair"
    end

(*** gamma uniq ***)
let flag_gamma_duplicates = ref false
let gamma_uniq : config_pair -> config_pair =
  fun ({a; c1; c2} as cfg_pair) ->
  if not !flag_gamma_duplicates then cfg_pair
  else
    begin
  match c1 , c2 with
  | None , None -> cfg_pair
  | Some ({g = g1; s = s1} as c1) , Some ({g = g2; s = s2} as c2) ->
     let to_delete = gama_dup_indices (g_to_list g1) (g_to_list g2) s1 s2 in
     let new_g1 = g_filter (fun k _ -> IntSet.mem k to_delete) g1 in
     let new_g2 = g_filter (fun k _ -> IntSet.mem k to_delete) g2 in
     {cfg_pair with 
                    c1 = Some {c1 with g = new_g1};
                    c2 = Some {c2 with g = new_g2}}
  | Some ({g = g1; s = s1} as c1) , None ->
     let to_delete = gama_dup_indices (g_to_list g1) (g_to_list g1) s1 s1 in
     let new_g1 = g_filter (fun k _ -> IntSet.mem k to_delete) g1 in
     {cfg_pair with
                    c1 = Some {c1 with g = new_g1};
                    c2 = None}
  | None , Some ({g = g2; s = s2} as c2) ->
     let to_delete = gama_dup_indices (g_to_list g2) (g_to_list g2) s2 s2 in
     let new_g2 = g_filter (fun k _ -> IntSet.mem k to_delete) g2 in
     {cfg_pair with
                    c1 = None;
                    c2 = Some {c2 with g = new_g2}}
    end

(********************
 * UP-TO TECHNIQUES *
 ********************)
(* up-to separation *)
let flag_sep = ref false

let upto_separation : config_pair -> config_pair =
  fun cfg_pair ->
  if not !flag_sep then cfg_pair
  else
    begin
      print_debug_sep "up-to separation called";

      let c1 , c2 = cfg_pair.c1 , cfg_pair.c2 in  
      match c1,c2 with
      | None , _ -> print_debug_sep "LHS bot"; cfg_pair
      | _ , None -> print_debug_sep "RHS bot"; cfg_pair
      | Some c1, Some c2 ->
         begin
           let exp_of_option =
             function Some e -> e | None -> failwith "upto_separation: None expression" in
           let names_of_bindings s bs =
             List.map (fun (k,v) -> k , names_of_value v s empty_conf_names) bs in
           let g1_kns = names_of_bindings c1.s (IntMap.bindings c1.g) in
           let g2_kns = names_of_bindings c2.s (IntMap.bindings c2.g) in
           let e1_ns = names_of_cek_exp (exp_of_option c1.e) c1.s empty_conf_names in
           let e2_ns = names_of_cek_exp (exp_of_option c2.e) c2.s empty_conf_names in
           let keys_to_remove = find_keys_to_remove g1_kns g2_kns e1_ns e2_ns in

           print_debug_sep (Printf.sprintf "Pre G1: %s" (string_of_g c1.g));
           
           let remove_keys ls gmap1 gmap2 =
             List.fold_left
               (fun (map1,map2) k -> print_debug_sep (Printf.sprintf "index removed: %d" k);
                                     IntMap.remove k map1,
                                     IntMap.remove k map2) (gmap1,gmap2) ls in
           
           let new_g1,new_g2 = remove_keys keys_to_remove c1.g c2.g in

           print_debug_sep (Printf.sprintf "Post G1: %s" (string_of_g new_g1));
           
           {cfg_pair with c1 = Some {c1 with g = new_g1};
                          c2 = Some {c2 with g = new_g2}}
         end
     end


(* up-to name reuse *)
let flag_nr = ref false

let get_eframe_names : (eval_cxt * store) option -> (conf_names * store) option = 
  fun es ->
  match es with
  | None -> None
  | Some (eframe,s) -> Some (names_of_context eframe s empty_conf_names , s)

let get_value_names : (value * store) option -> (conf_names * store) option = 
  fun vs ->
  match vs with
  | None -> None
  | Some (v,s) -> Some (names_of_value v s empty_conf_names , s)

let skip_name_reuse : (conf_names * store) option -> (conf_names * store) option -> bool =
  fun ns1 ns2 ->
  match ns1,ns2 with
  | None,None -> failwith "skip name reuse: expected at least one config"
  | None,Some (n2,s2) -> is_ho_in_locs n2.locs s2
  | Some (n1,s1),None -> is_ho_in_locs n1.locs s1
  | Some (n1,s1),Some (n2,s2) -> is_ho_in_locs n1.locs s1 || is_ho_in_locs n2.locs s2

(* up-to identity *)
let flag_id = ref false

(* up-to generalisation *)
let flag_generalise = ref false
let flag_gen_succeeded = ref false
let set_gen_success () = flag_gen_succeeded := true
let retry_fun = ref (fun () -> ())
let twice_twice = ref false

let apply_generalisation func1 func2 s1 s2 sigma =
  let sigma1 , countersigma1 , abs1 , newls1 , pos1 , gen1 =
    match func1 with
    | Some (FunVal (_ , _ , _ , _ , _ , gen)) ->
       generalise_conditions gen sigma (fst sigma , fst sigma)
         s1 None !flag_generalise print_debug_generalise
    | _ -> sigma , (fst sigma , fst sigma) , None , [] , None , None
  in
  let sigma2 , countersigma2 , abs2 , newls2 , pos2 , gen2 =
    match func2 with
    | Some (FunVal (_ , _ , _ , _ , _ , gen)) ->
       generalise_conditions gen sigma1 countersigma1
         s2 abs1 !flag_generalise print_debug_generalise 
    | _ -> sigma1 , countersigma1 , None , [] , None , None
  in
  let s1 =
    match func1 with
    | Some (FunVal (_ , _ , _ , _ , _ , gen)) ->
       generalise gen s1 newls1 countersigma2 pos1 !flag_generalise set_gen_success
    | _ -> s1
  in
  let s2 =
    match func2 with
    | Some (FunVal (_ , _ , _ , _ , _ , gen)) ->
       generalise gen s2 newls2 countersigma2 pos2 !flag_generalise set_gen_success
    | _ -> s2
  in
  s1,s2,sigma2,gen1,gen2

(* up-to generalisable nested opponent call *)
let flag_reentry = ref false

let skip_nested_ocall gen1 gen2 ocall_stack index2 g1_map g2_map s1 s2 =
  if !flag_generalise && !flag_reentry
  then
    begin
      match gen1 , gen2 with
      | None , None -> false
      | _ ->
         begin
           match List.find_opt (fun {oc_i} -> index2 = oc_i) ocall_stack with
           | None -> false
           | Some {oc_i;oc_gs1;oc_gs2} ->
              let ss_of_kv g_map = 
                List.fold_right
                  (fun (k,v) acc ->
                    let s_of_v = string_of_val v in
                    let s_of_pair = Printf.sprintf "%d,%s" k s_of_v in
                    StringSet.add s_of_pair acc)
                  (g_to_list g_map) StringSet.empty
              in
              let prune_store s gen =
                match gen with
                | None -> s
                | Some (_,ls, _) -> 
                   List.fold_right (fun ((l,_),_) new_s -> StoreMap.remove l new_s) ls s
              in
              match oc_gs1 , oc_gs2 with
              | None , None -> failwith "skip_nested_ocall: double None config"
              | Some (oc_g1 , oc_s1) , Some (oc_g2 , oc_s2) ->
                 let g1_ss,ocg1_ss , g2_ss,ocg2_ss =
                   ss_of_kv g1_map , ss_of_kv oc_g1 ,
                   ss_of_kv g2_map , ss_of_kv oc_g2
                 in
                 
                 let s1' = prune_store s1 gen1 in
                 let oc_s1' = prune_store oc_s1 gen1 in
                 let s2' = prune_store s2 gen2 in
                 let oc_s2' = prune_store oc_s2 gen2 in
                 
                 (StringSet.subset g1_ss ocg1_ss)
                 && (StringSet.subset g2_ss ocg2_ss)
                 && ((string_of_s s1') = (string_of_s oc_s1'))
                 && ((string_of_s s2') = (string_of_s oc_s2'))
              | Some (oc_g1 , oc_s1) , None ->
                 let g1_ss,ocg1_ss =
                   ss_of_kv g1_map , ss_of_kv oc_g1
                 in
                 
                 let s1' = prune_store s1 gen1 in
                 let oc_s1' = prune_store oc_s1 gen1 in
                 
                 (StringSet.subset g1_ss ocg1_ss)
                 && ((string_of_s s1') = (string_of_s oc_s1'))
              | None , Some (oc_g2 , oc_s2) ->
                 let g2_ss,ocg2_ss =
                   ss_of_kv g2_map , ss_of_kv oc_g2
                 in
                 
                 let s2' = prune_store s2 gen2 in
                 let oc_s2' = prune_store oc_s2 gen2 in
                 
                 (StringSet.subset g2_ss ocg2_ss)
                 && ((string_of_s s2') = (string_of_s oc_s2'))
         end
    end
  else false


(*** opponent transition functions ***
 *
 * Accepts an LTS configuration
 * Returns:
 * - A list of config_pair: this is the list of next configurations
 *
 * Invariant: all returned configurations are proponent configurations
 *
 * Top-level function:
 * - op_transitions
 *
 * *)

(* mk_op_tuple is the core of name-reuse *)
let rec mk_op_tuple_from_type : abs_set -> Type.t -> IntSet.t -> bool -> value * abs_set * IntSet.t =
  fun a in_type used_ids skip_name_reuse ->
  match in_type with
  | Type.UnitT -> ConstVal UnitConst , a , used_ids
  | BoolT | IntT ->
     let new_id , new_a = abs_next_id in_type a in
     AbsCon (new_id, in_type, Ast.default_acname) , new_a , IntSet.add new_id used_ids
  | Type.FunT (args,ret_type) ->
     begin
       match args with
       | arg_type::[] ->
          begin
            let make_new_abs () =
              let new_id , new_a = abs_next_id in_type a in
              AbsFun (new_id, arg_type, ret_type, Ast.default_afname) , new_a , IntSet.add new_id used_ids
            in
            if skip_name_reuse || (not !flag_nr) then make_new_abs ()
            else
              begin
                match TypeMap.find_opt in_type a.ti with
                | None -> make_new_abs ()
                | Some id_set ->
                   begin
                     match get_reusable_name id_set used_ids with
                     | None -> make_new_abs ()
                     | Some (new_id , new_used_ids) ->
                        print_debug_nr (Printf.sprintf "id reused: %d" new_id);
                        AbsFun (new_id, arg_type, ret_type, "af") , a , new_used_ids
                   end
              end
          end
       | _ -> failwith "get fun type: unexpected type given"
     end
  | TupleT ls ->
     let new_ls, new_a, new_used_ids =
       List.fold_right
         (fun t (vs,a,used) ->
           let new_item,new_a,new_used = mk_op_tuple_from_type a t used skip_name_reuse in
           new_item::vs,new_a,new_used) ls ([],a,used_ids)
     in
     TupleVal new_ls , new_a , new_used_ids
  | VarT _ -> failwith "mk op tuple: only closed types at LTS, VarT shouldn't appear."

let components_from_type a k_type ns1 ns2 newtr =
  let skip = skip_name_reuse ns1 ns2 in
  let old_names =
    match ns1,ns2 with
    | None,None -> IntSet.empty
    | Some(n1,s1),None -> intset_of_namemap n1.abs
    | None,Some(n2,s2) -> intset_of_namemap n2.abs
    | Some(n1,s1), Some(n2,s2) ->
       IntSet.union (intset_of_namemap n1.abs) (intset_of_namemap n2.abs)
  in
  let new_abs , new_a , used_ids = mk_op_tuple_from_type a k_type old_names skip in
  let new_trace = newtr new_abs in
  (new_abs , new_trace , new_a)

let op_ret_trans (({a; c1; c2; tr} as cfg_pair):config_pair) =
  let newtr new_abs = (OpRet new_abs) :: tr in
  let components_from_type_frame a k_type es1 es2 =
    let ns1 = get_eframe_names es1 in
    let ns2 = get_eframe_names es2 in
    components_from_type a k_type ns1 ns2 newtr
  in
  
  match (c1, c2) with
  | None, None -> []

  | Some ({k = (k1_nxt,k1_type) :: k1_rest; e = None} as c01), None ->
     let (new_abs , new_trace , new_a) = components_from_type_frame a k1_type (Some (k1_nxt,c01.s)) None in
     {cfg_pair with
       a = new_a;
       c1 = Some {c01 with k = k1_rest;e = Some {ecxt = k1_nxt;e = ValExp (new_abs, None)}};
       c2 = None;
       tr = new_trace} :: []

  | None, Some ({k = (k2_nxt,k2_type) :: k2_rest ; e = None} as c02) ->
     let (new_abs , new_trace , new_a) = components_from_type_frame a k2_type None (Some (k2_nxt,c02.s)) in
     {cfg_pair with
       a = new_a;
       c1 = None;
       c2 = Some {c02 with k = k2_rest;e = Some {ecxt = k2_nxt;e = ValExp (new_abs, None)}};
       tr = new_trace} :: []

  | Some ({k = (k1_nxt,k1_type) :: k1_rest; e = None} as c01),
    Some ({k = (k2_nxt,k2_type) :: k2_rest; e = None} as c02) ->
     
     if k1_type <> k2_type then failwith "oret: evaluation context type mismatch" else
       (** YY: k_type needs to be the same. **)
       
       let (new_abs , new_trace, new_a) = components_from_type_frame a k2_type
                                            (Some (k1_nxt,c01.s)) (Some (k2_nxt,c02.s)) in
       {cfg_pair with
         a = new_a;
         c1 = Some {c01 with k = k1_rest; e = Some {ecxt = k1_nxt; e = ValExp (new_abs, None)}};
         c2 = Some {c02 with k = k2_rest; e = Some {ecxt = k2_nxt; e = ValExp (new_abs, None)}};
         tr = new_trace} :: []

  (* valid opponent configurations that cannot return *)
  | Some {k = [] ; e = None}, Some {k = []; e = None} -> []

  (* anything else is invalid here *)
  | _ -> failwith "erroneous configurations in opponent return transition"
;;

let get_fun_type = function
  | Type.FunT (argt::[],rett) -> argt , rett
  | t -> failwith ("get_fun_type: expected function, got " ^ (Type.string_of_t t))

let rec type_of_value = function
  | ConstVal c ->
     begin
       match c with
       | IntConst i -> Type.IntT
       | BoolConst b -> Type.BoolT
       | UnitConst -> Type.UnitT
     end
  | FunVal (func_name, ret_type, arg, arg_type, body, _) -> Type.FunT ([arg_type],ret_type)
  | AbsCon (id, typ, name) -> typ
  | AbsFun (id, t1, t2, name) -> Type.FunT ([t1],t2)
  | TupleVal ls -> TupleT (List.map type_of_value ls)

let op_call_trans ({a; c1; c2; tr; bound = (bound10,bound20); sigma; ocall_stack} :config_pair) =
  let op_reduce_app vop varg bound =
    (* HACK: the code below assumes that the bound is decreased by 1 by reduce_app *)
    match reduce_app (Substitution.refresh_bound_ids_val vop) varg bound with 
    | None -> (* stuck due to application of abstract constant or bad types *)
        {ecxt = []; e = AppExp (ValExp (vop, None), ValExp (varg, None), None)}
    | Some (new_e, new_bound) ->
        {ecxt = []; e = new_e}
  in
  if min bound10 bound20 = 0 then []
  else
    begin
      let newtr i new_abs = OpCall (i, new_abs) :: tr in
      let components_from_type_value a k_type vs1 vs2 i =
        let ns1 = get_value_names vs1 in
        let ns2 = get_value_names vs2 in
        components_from_type a k_type ns1 ns2 (newtr i)
      in
      match (c1, c2) with
      | (None, None) -> []
      
      | (Some ({g = g1_map; e = None} as c01), None) ->
         (List.fold_left
            (fun out_lst (index,func) ->
              if not(is_ho_value func)
              then failwith "ocall: g shouldn't contain ground-type values" else

                let s1,_,sigma2,gen1,_ =
                  apply_generalisation (Some func) None c01.s c01.s sigma in
                let gen_skip_call =
                  skip_nested_ocall gen1 None ocall_stack index g1_map g1_map s1 s1
                in

                if gen_skip_call then
                  ({a = a;
                    c1 = Some {c01 with s = s1};
                    c2 = None;
                    tr = tr;
                    bound = (bound10,bound20);
                    sigma = sigma2;
                    ocall_stack} :: out_lst)
                else
                
                let arg_type, ret_type = get_fun_type (type_of_value func) in
                let new_abs , new_trace , new_a =
                  components_from_type_value a arg_type (Some (func,s1)) None (PrIndex index)
                in
                ({a = new_a;
                  c1 = Some {c01 with e = Some (op_reduce_app func new_abs bound10); s = s1};
                  c2 = None;
                  tr = new_trace;
                  bound = (bound10-1,bound20); sigma = sigma2;
                  ocall_stack =  {oc_i = index;
                                  oc_gs1 = Some (c01.g , s1);
                                  oc_gs2 = None} :: ocall_stack} :: out_lst))
            []
            (g_to_list g1_map))

      | (None, Some ({g = g2_map; e = None} as c02)) ->
         (List.fold_left
            (fun out_lst (index,func) ->

              if not(is_ho_value func)
              then failwith "ocall: g shouldn't contain ground-type values" else

                let _,s2,sigma2,_,gen2 =
                  apply_generalisation None (Some func) c02.s c02.s sigma in
                let gen_skip_call =
                  skip_nested_ocall None gen2 ocall_stack index g2_map g2_map s2 s2
                in

                if gen_skip_call then
                  ({a = a;
                    c1 = None;
                    c2 = Some {c02 with s=s2};
                    tr = tr;
                    bound = (bound10,bound20);
                    sigma = sigma2;
                    ocall_stack} :: out_lst)
                else

                let arg_type, ret_type = get_fun_type (type_of_value func) in
                let new_abs , new_trace , new_a =
                  components_from_type_value a arg_type None (Some (func,s2)) (PrIndex index)
                in
                ({a = new_a;
                  c1 = None;
                  c2 = Some {c02 with e = Some (op_reduce_app func new_abs bound20); s = s2};
                  tr = new_trace;
                  bound = (bound10,bound20-1); sigma = sigma2;
                  ocall_stack =  {oc_i = index;
                                  oc_gs1 = None;
                                  oc_gs2 = Some (c02.g , s2)} :: ocall_stack} :: out_lst))
            []
            (g_to_list g2_map))

      | (Some ({g = g1_map; e = None} as c01), Some ({g = g2_map; e = None} as c02)) ->         
         let (_, out_lst) =
           (List.fold_left
              (fun (g2_lst_in, out_lst) (index1,func1) ->
                match g2_lst_in with
                | [] -> print_endline "g1 and g2 do not have same length"; assert false
                | (index2,func2) :: g2_rest ->

                   let s1,s2,sigma2,gen1,gen2 =
                     apply_generalisation (Some func1) (Some func2) c01.s c02.s sigma in
                   let gen_skip_call =
                     skip_nested_ocall gen1 gen2 ocall_stack index2 g1_map g2_map s1 s2
                   in

                   if gen_skip_call then
                     (g2_rest,
                      {a = a;
                       c1 = Some {c01 with s=s1};
                       c2 = Some {c02 with s=s2};
                       tr = tr;
                       bound = (bound10,bound20);
                       sigma = sigma2;
                       ocall_stack} :: out_lst)
                   else
                     
                   if (type_of_value func1) <> (type_of_value func2)
                   then failwith "ocall: type mismatch" else (
                     if index1 <> index2
                     then failwith "ocall: index mismatch" else (

                       if not(is_ho_value func1)
                       then failwith "ocall: g shouldn't contain ground-type values" else (

                         let arg_type, ret_type = get_fun_type (type_of_value func1) in
                         let new_abs , new_trace , new_a =
                           components_from_type_value a arg_type
                             (Some (func1,c01.s)) (Some (func2,c02.s)) (PrIndex index1)
                         in

                         (g2_rest,
                          {a = new_a;
                           c1 = Some {c01 with e = Some (op_reduce_app func1 new_abs bound10); s=s1};
                           c2 = Some {c02 with e = Some (op_reduce_app func2 new_abs bound20); s=s2};
                           tr = new_trace;
                           bound = (bound10-1,bound20-1); sigma = sigma2;
                           ocall_stack =  {oc_i = index2;
                                           oc_gs1 = Some (c01.g , s1);
                                           oc_gs2 = Some (c02.g , s2)} :: ocall_stack} :: out_lst)))))
              (g_to_list g2_map, [])
              (g_to_list g1_map))
         in out_lst

      (* anything else is invalid here *)
      | _ -> failwith "Internal Error! erroneous configurations in opponent call transition"
    end

let op_coterminate ({c1; c2; tr} as cfg_pair) =
  match (c1, c2) with
  | (None, None) -> (true, [])
  (* relies on invariant that k's have same length in both configs *)
  | (Some {e = None}, Some {e = None}) -> (true, [])  
  | (Some {k = []; e = None}, None) -> (false, (Markup "only LHS terminates") :: tr)
  | (None, Some {k = []; e = None}) -> (false, (Markup "only RHS terminates") :: tr)
  | (None, Some {e = None}) -> (true, [])
  | (Some {e = None}, None) -> (true, [])
  (* anything else is invalid here *)
  | _ -> ((print_endline "Internal Error! erroneous configurations in opponent termination transition");
          print_endline ("c1 = " ^ (string_of_cfg_pair cfg_pair));
          assert (false))

(* op_transitions: top-level for opponent configurations
 *
 * Accepts a double configuration
 * Produces a set of dbl_config
 * bisimulation can fail here only when checking co-termination
 * *)
let op_transitions cfg_pair =
  let (success, tr) = op_coterminate cfg_pair in
  if not success then
    if not !flag_gen_succeeded then
      begin
        Printf.printf "Bisimulation failed! Failing trace:\n%s\n\n" (string_of_trace tr);
        if not(is_sigma_empty (fst cfg_pair.sigma)) then
          begin
            Printf.printf "Symbolic Environment:\n %s\n\n"
              (string_of_sigma (fst cfg_pair.sigma));
            if (check_sat_sigma (fst cfg_pair.sigma))
            then Printf.printf "Satisfying Assignment:\n%s\n" (get_model_s ())
            else failwith "sigma should be sat but isn't"
          end;
        exit exit_ineq
      end
    else
      begin
        begin
          if !flag_generalise then
            begin
              Printf.printf "Potential failing trace found:\n %s\n\n" (string_of_trace tr);
              print_endline "However, state generalisations were used so inequivalences may be unsound.";
              print_endline "***Retrying with state generalisations off***\n";
              flag_generalise := false;
              twice_twice := true;
              !retry_fun ()
            end
          else
            begin
              Printf.printf "Bisimulation failed! Real failing trace found:\n %s\n\n" (string_of_trace tr);
              exit exit_ineq
            end
        end;
        exit exit_unknown
      end

  ;
  (op_call_trans cfg_pair) @ (op_ret_trans cfg_pair) (* explore op-call moves before op-ret *)


(*** proponent transition functions ***
 *
 * Accepts an LTS configuration and a bound
 * Returns:
 * - A list of (config_pair * bound): this is the list of next configurations
 *
 * Invariant: all returned configurations are opponent configurations
 *
 * Top-level function:
 * - pr_transitions
 *
 * *)

let ret_type_of_fun = function
  | FunVal (func_name, ret_type, arg, arg_type, body, _) -> ret_type
  | AbsFun (id, arg_type, ret_type, name) -> ret_type
  | _ -> failwith "arg type of function: not a function"

let rec collect_funcs v g =
  let pridx_of_snd (a,b) = (a,PrIndex b) in
  match v with
  | ConstVal _ -> g , PrConst v
  | FunVal   _ -> pridx_of_snd (g_add v g)
  | AbsCon   _ -> g , PrConst v
  | AbsFun   _ -> pridx_of_snd (g_add v g)
  | TupleVal ls ->
     let new_g, idx_list = 
       List.fold_right
         (fun v (g',idx_acc) ->
           let new_g , new_prindex = collect_funcs v g' in
           new_g , new_prindex::idx_acc) ls (g,[])
     in new_g , PrTuple idx_list

(* YY-COMMENT: this appears to be reducing a single config. *)
(* YY-COMMENT: return type: (Either config * Either transition label * Bound * Sigma) *)
let config_transition cfg bound0 sigma0 =
  print_debug_sigma (Printf.sprintf "produced sigma: %s" (string_of_sigma (fst sigma0)));
  match cfg with
  | None -> (None, None, bound0, sigma0) :: []    (* this is a bottom configuration *)
  | Some {e = None} -> failwith "Internal Error! opponent configuration appeared at proponent move"
  | Some ({s = s0; e = Some e0} as cfg0) ->
     begin
       let next_confs = big_step {Reductions_ast.s = s0; e = e0} bound0 sigma0 in
       let process_conf ({Reductions_ast.s = s1; e = e1}, bound1, sigma1) =
         (* bound exhausted during reduction -- tau is used as a flag to the caller  *)
         if bound1 = 0 then (None, Some Tau, 0, sigma0)
         else
           begin
             match e1 with
             | {ecxt = []; e = ValExp (v, _)} ->
                (** a return transition **)
                (* collect all functions in the value *)
                let new_g,new_prval = collect_funcs v cfg0.g in
                (Some {cfg0 with g = new_g; s = s1; e = None},
                 Some (PrRet new_prval), bound1, sigma1)
             | {ecxt = AppRandECxt ((AbsFun (afid, t1, t2, str) as v1), _) :: ec_rest; e = ValExp (v2, _)} ->
                (** a call transition **)
                (* collect all functions in the value *)
                let new_g,new_prval = collect_funcs v2 cfg0.g in
                (Some {g = new_g; k = (ec_rest , t2) :: cfg0.k; s = s1; e = None},
                 Some (PrCall (v1,new_prval)), bound1, sigma1)
             | _ -> (* otherwise stuck term*)
                (None, None, bound1, sigma1)
           end
       in List.map process_conf next_confs
     end

let pr_transitions ({c1; c2; tr; bound = (bound10, bound20); sigma = sigma0} as cfg_pair) =
  print_debug_sigma (Printf.sprintf "sigma0: %s" (string_of_prop (prop_of_sigma (fst sigma0))));
  print_debug_traces (string_of_trace cfg_pair.tr);
  print_debug_confs (string_of_cfg_pair cfg_pair);

  (* LHS Challenge *)
  (* YY-COMMENT: first try to transition C1 with bound10 *)

  (* need to first call config_transition to produce all reachable confs *)
  (* then, for each conf, produce all reachable c2 confs that satisfy the SIGMA *)

  let c1_confs = config_transition c1 bound10 sigma0 in
  
  let cases_of_c1 conf rest =
    match conf with
    | (None, Some Tau, 0, sigma1) -> (* no challenge from LHS - exhausted bound *)
       bound_reached := true;
       rest
    | (None, None, bound1, sigma1) -> (* no challenge from LHS - bot *)
       begin
         let c2_confs = config_transition c2 bound20 sigma1 in
         let cases_of_c2 conf rest2 =
           match conf with
           | (None, Some Tau, 0, sigma2) -> (* run out of bound *)
              bound_reached := true;
              rest2
           | (None, None, bound2, sigma2) -> (* both bot *)
              rest2
           (* YY-COMMENT: transition of C2 with bound20 results in bound2 *)
           | (Some c21, Some label2, bound2, sigma2) -> (* challenge from RHS matched by a move *)
              let new_tr = label2 :: (if c1 = None then tr else (Markup "entering LHS=bot") :: tr) in
              let func2 =
                match cfg_pair.ocall_stack with
                | [] -> None
                | {oc_i; oc_gs1 = _; oc_gs2 = Some (oc_g2,oc_s2)} :: _ ->
                   (* TODO: not checking for None because it may be that a proponent call changed it?*)
                   IntMap.find_opt oc_i oc_g2
                | _ -> failwith "Pr:None,Some: ill-formed oc stack"
              in
              let gen_s1,gen_s2,gen_sigma2,gen1,gen2 =
                match func2 with
                | None -> c21.s,c21.s,sigma2,None,None
                | Some func2 ->
                   apply_generalisation None (Some func2) c21.s c21.s sigma2
              in
              let new_oc_stack = 
                match label2 with
                | PrRet _ -> List.tl cfg_pair.ocall_stack
                | PrCall _ -> cfg_pair.ocall_stack
                | _ -> failwith "not Pr label"
              in
              {cfg_pair with c1 = None;
                             c2 = Some {c21 with s = gen_s2};
                             tr = new_tr;
                             bound = (bound1, bound2);
                             sigma = gen_sigma2;
                             ocall_stack = new_oc_stack} :: rest2
           | (_, _, _, _) -> (print_endline "Internal error! unexpected value"; assert false;)
         in
         List.fold_right (fun conf rest -> cases_of_c2 conf rest) c2_confs rest
       end
    | (Some c11, Some label1, bound1, sigma1) -> (* challenge from LHS to be matched by RHS *)
       begin
         (* YY-COMMENT: since C1 with bound10 succeeded, run C2 with bound20 *)
         let c2_confs = config_transition c2 bound20 sigma1 in
         let cases_of_c2 conf rest2 =
           match conf with
           | (None, Some Tau, 0, sigma2) -> (* RHS run out of bound *)
              bound_reached := true;
              rest2

           | (None, None, bound2, sigma2) -> (* RHS got stuck or became bot*)
              let new_tr = label1 :: (if c2 = None then tr else (Markup "entering RHS=bot") :: tr) in
              print_debug_traces (string_of_trace [label1]);
              print_debug_confs (string_of_cfg c11);
              let func1 =
                match cfg_pair.ocall_stack with
                | [] -> None
                | {oc_i; oc_gs1 = Some (oc_g1,oc_s1); oc_gs2 = _} :: _ ->
                   (* TODO: not checking for None because it may be that a proponent call changed it?*)
                   IntMap.find_opt oc_i oc_g1
                | _ -> failwith "Pr:Some,None: ill-formed oc stack"
              in
              let gen_s1,_,gen_sigma2,gen1,_ =
                match func1 with
                | None -> c11.s,c11.s,sigma2,None,None
                | Some func1 ->
                   apply_generalisation (Some func1) None c11.s c11.s sigma2
              in
              let new_oc_stack = 
                match label1 with
                | PrRet _ -> List.tl cfg_pair.ocall_stack
                | PrCall _ -> cfg_pair.ocall_stack
                | _ -> failwith "not Pr label"
              in
              {cfg_pair with c1 = Some {c11 with s = gen_s1};
                             c2 = None ; tr = new_tr; bound = (bound1, bound2);
                             sigma = gen_sigma2;
                             ocall_stack = new_oc_stack} :: rest2
           | (Some c21, Some label2, bound2, sigma2) ->
              (** STRUCTURAL EQUALITY OF LABELS IS TOO STRONG because of symbolic names. **)
              (*Printf.printf "label1: %s\nlabel2: %s" (string_of_trans label1) (string_of_trans label2);*)
              
              (* no need to traverse label to make sure all constants are the same
                 we only have constants, tuples, or indexes. So structural eq suffices.*)
              if label1 = label2 then
                begin
                  let func1,func2 =
                    match cfg_pair.ocall_stack with
                    | [] -> None,None
                    | {oc_i; oc_gs1 = Some (oc_g1,oc_s1); oc_gs2 = Some (oc_g2,oc_s2)} :: _ ->
                       IntMap.find_opt oc_i oc_g1 , IntMap.find_opt oc_i oc_g2
                    | _ -> failwith "Pr:label1=label2: unexpected ocall_stack"
                  in
                  let gen_s1,gen_s2,gen_sigma2,gen1,gen2 =
                    match func1,func2 with
                    | None , None -> c11.s,c21.s,sigma2,None,None
                    | Some func1, Some func2 ->
                       apply_generalisation (Some func1) (Some func2) c11.s c21.s sigma2
                    | _ -> failwith "PrRet Generalisation: ill-formed oc stack"
                  in
                  let new_oc_stack = 
                    match label1 with
                    | PrRet _ ->
                       begin
                         match cfg_pair.ocall_stack with
                         | [] -> []
                         | x::xs -> xs
                       end 
                    | PrCall _ -> cfg_pair.ocall_stack
                    | _ -> failwith "not Pr label"
                  in
                  let new_cfg_pair =
                    {cfg_pair with c1 = Some {c11 with s = gen_s1};
                                   c2 = Some {c21 with s = gen_s2}; tr = label1 :: tr;
                                   bound = (bound1, bound2); sigma = gen_sigma2;
                                   ocall_stack = new_oc_stack}
                  in
                  new_cfg_pair :: rest2
                end
              else
                (* labels are not equal... time to check *)
                begin
                  (* PrIndex of int | PrConst of value | PrTuple of prvalue list *)
                  let check_congruence_sat v1 v2 sigma =
                    print_debug_sigma "entered check_congruence_sat";
                    (* gets two values, returns pair A,B,C *)
                    (* A: v1 == v2? *)
                    (* B: formula c1 <> c2 *)
                    (* C: f1 == f2? *)
                    let rec get_congruence_prop v1 v2 const_eq fun_eq nc_sigma =
                      match v1,v2 with
                      (* Int, Bool, Unit, AbsCons or AbsFun *)
                      | PrConst (ConstVal UnitConst),PrConst (ConstVal UnitConst) ->
                         true && const_eq , fun_eq , nc_sigma
                      | PrConst (ConstVal (IntConst i1)),PrConst (ConstVal (IntConst i2)) ->
                         (i1=i2) && const_eq , fun_eq , nc_sigma
                      | PrConst (ConstVal (BoolConst b1)),PrConst (ConstVal (BoolConst b2)) ->
                         (b1=b2) && const_eq , fun_eq , nc_sigma
                      | PrConst (AbsCon (id1,typ1,name1)), PrConst (AbsCon (id2,typ2,name2)) ->
                         begin
                           let new_nc_dtree = dt_update_id (snd nc_sigma) id1 [Some id2] in
                           match typ1,typ2 with
                           | Type.BoolT,Type.BoolT  ->
                              let new_nc_sigma = sigma_add_bvar_neq (id1,name1) (id2,name2) (fst nc_sigma) in
                              const_eq , fun_eq , (new_nc_sigma , new_nc_dtree)
                           | Type.IntT,Type.IntT  ->
                              let new_nc_sigma = sigma_add_ivar_neq (id1,name1) (id2,name2) (fst nc_sigma) in
                              const_eq , fun_eq , (new_nc_sigma , new_nc_dtree)
                           | _ -> failwith "get_congruence_prop: only x1 = x2 of bool/int allowed"
                         end
                      | PrConst (AbsCon (id1,typ1,name1)), PrConst (ConstVal v) ->
                         begin
                           match v with
                           | IntConst i ->
                              let new_nc_sigma = sigma_add_iconst_neq (id1,name1) i (fst nc_sigma) in
                              const_eq , fun_eq , (new_nc_sigma , snd nc_sigma)
                           | BoolConst b ->
                              let new_nc_sigma = sigma_add_bconst_neq (id1,name1) b (fst nc_sigma) in
                              const_eq , fun_eq , (new_nc_sigma , snd nc_sigma)
                           | _ -> failwith "get_congruence_prop: only x = c of bool/int allowed"
                         end
                      | PrConst (ConstVal v), PrConst (AbsCon (id1,typ1,name1)) ->
                         begin
                           match v with
                           | IntConst i ->
                              let new_nc_sigma = sigma_add_iconst_neq (id1,name1) i (fst nc_sigma) in
                              const_eq , fun_eq , (new_nc_sigma , snd nc_sigma)
                           | BoolConst b ->
                              let new_nc_sigma = sigma_add_bconst_neq (id1,name1) b (fst nc_sigma) in
                              const_eq , fun_eq , (new_nc_sigma , snd nc_sigma)
                           | _ -> failwith "get_congruence_prop: only x = c of bool/int allowed"
                         end
                      | PrIndex i1, PrIndex i2 -> const_eq , i1=i2 && fun_eq , nc_sigma
                      | PrTuple (x::xs), PrTuple (y::ys) ->
                         let cons1,funs1,nc_sig1 = get_congruence_prop x y const_eq fun_eq nc_sigma in
                         get_congruence_prop (PrTuple xs) (PrTuple ys) cons1 funs1 nc_sig1
                      | PrTuple [], PrTuple [] -> const_eq , fun_eq , nc_sigma
                      | _ , _ -> failwith "pr move: congruence mismatch"
                    in
                    let cons_eq,funs_eq,nc_sigma = get_congruence_prop v1 v2 true true sigma in
                    print_debug_sigma (Printf.sprintf "cong sigma: %s" (string_of_sigma (fst sigma)));
                    print_debug_sigma (Printf.sprintf "not cong sigma: %s" (string_of_sigma (fst nc_sigma)));
                    assert(funs_eq);
                    
                    let labels_different =
                      if cons_eq
                      then (* concrete vals in tuple are equal, check symbolic vals *)
                        check_sat_sigma (fst (nc_sigma))                
                      else (* concrete vals in tuple are not equal, no need to check symbolic vals *)
                        true 
                    in
                    print_debug_sigma (Printf.sprintf "original dtree: %s"
                                         (string_of_dtree (snd sigma)));
                    print_debug_sigma (Printf.sprintf "notcong dtree: %s"
                                         (string_of_dtree (snd nc_sigma)));
                    not labels_different ,
                    (if labels_different then nc_sigma else sigma)
                  in
                  let generalise_on_sigma new_sigma =
                    let func1,func2 =
                      match cfg_pair.ocall_stack with
                      | [] -> None,None
                      | {oc_i; oc_gs1 = Some (oc_g1,oc_s1); oc_gs2 = Some (oc_g2,oc_s2)} :: _ ->
                         IntMap.find_opt oc_i oc_g1 , IntMap.find_opt oc_i oc_g2
                      | _ -> failwith "PrRet Generalisation: ill-formed oc stack (1)"
                    in
                    match func1,func2 with
                    | None , None -> c11.s,c21.s,new_sigma,None,None
                    | Some func1, Some func2 ->
                       apply_generalisation (Some func1) (Some func2) c11.s c21.s new_sigma
                    | _ -> failwith "PrRet Generalisation: ill-formed oc stack (2)"
                  in
                  
                  match label1,label2 with
                  | PrRet prv1, PrRet prv2 ->
                     (* YY: is sigma2 which contains sigma1 sat? *)
                     let labels_equal,new_sigma = check_congruence_sat prv1 prv2 sigma2 in
                     let gen_s1,gen_s2,gen_sigma2,gen1,gen2 = generalise_on_sigma new_sigma in
                       
                     if labels_equal
                     then
                       begin
                         (* YY: yes, they are equivalent under some assignment *)
                         {cfg_pair with c1 = Some {c11 with s = gen_s1};
                                        c2 = Some {c21 with s = gen_s2}; tr = label1 :: tr;
                                        bound = (bound1, bound2); sigma = (gen_sigma2);
                                        ocall_stack = List.tl cfg_pair.ocall_stack} :: rest2
                       end
                     else
                       begin
                         (* YY: no, so we enter bottom mode *)
                         {cfg_pair with c1 = Some {c11 with s = gen_s1};
                                        c2 = None;
                                        tr = label1 :: (Markup "RHS=bot") :: tr;
                                        bound = (bound1, bound2); sigma = (gen_sigma2);
                                        ocall_stack = List.tl cfg_pair.ocall_stack} ::
                           {cfg_pair with c1 = None;
                                          c2 = Some {c21 with s = gen_s2};
                                          tr = label2 :: (Markup "LHS=bot") :: tr;
                                          bound = (bound1, bound2); sigma = (gen_sigma2);
                                          ocall_stack = List.tl cfg_pair.ocall_stack} :: rest2
                       end
                  | PrCall (AbsFun (a1, _, _, _), prv1),
                    PrCall (AbsFun (a2, _, _, _), prv2) ->
                     (* YY: is sigma2 which contains sigma1 sat? *)
                     let labels_equal,new_sigma = check_congruence_sat prv1 prv2 sigma2 in
                     let gen_s1,gen_s2,gen_sigma2,gen1,gen2 = generalise_on_sigma new_sigma in
                     let new_oc_stack = 
                       match label1 with
                       | PrRet _ -> List.tl cfg_pair.ocall_stack
                       | PrCall _ -> cfg_pair.ocall_stack
                       | _ -> failwith "not Pr label"
                     in                     
                     if a1 = a2 && labels_equal
                     then
                       begin
                         (* YY: yes, they are equivalent under some assignment *)

                         {cfg_pair with c1 = Some {c11 with s = gen_s1};
                                        c2 = Some {c21 with s = gen_s2}; tr = label1 :: tr;
                                        bound = (bound1, bound2); sigma = gen_sigma2;
                                        ocall_stack = new_oc_stack} :: rest2
                       end
                     else
                       begin
                         (* YY: no, so we enter bottom mode *)
                         {cfg_pair with c1 = Some {c11 with s = gen_s1};
                                        c2 = None ;
                                        tr = label1 :: (Markup "RHS=bot") :: tr;
                                        bound = (bound1, bound2); sigma = gen_sigma2} ::
                           {cfg_pair with c1 = None;
                                          c2 = Some {c21 with s = gen_s2};
                                          tr = label2 :: (Markup "LHS=bot") :: tr;
                                          bound = (bound1, bound2); sigma = gen_sigma2;
                                          ocall_stack = new_oc_stack} :: rest2
                       end
                  | _ ->
                     let gen_s1,gen_s2,gen_sigma2,gen1,gen2 = generalise_on_sigma sigma2 in
                     let new_oc_stack = 
                       match label1 with
                       | PrRet _ -> List.tl cfg_pair.ocall_stack
                       | PrCall _ -> cfg_pair.ocall_stack
                       | _ -> failwith "not Pr label"
                     in                     

                     {cfg_pair with c1 = Some {c11 with s = gen_s1};
                                    c2 = None;
                                    tr = label1 :: (Markup "RHS=bot") :: tr;
                                    bound = (bound1, bound2); sigma = gen_sigma2} ::
                       {cfg_pair with c1 = None;
                                      c2 = Some {c21 with s = gen_s2};
                                      tr = label2 :: (Markup "LHS=bot") :: tr;
                                      bound = (bound1, bound2); sigma = gen_sigma2;
                                      ocall_stack = new_oc_stack} :: rest2
                end
           | (_, _, _, _) -> (print_endline "Internal error! unexpected value"; assert false;)
         in
         List.fold_right (fun conf rest -> cases_of_c2 conf rest) c2_confs rest
       end
    | (_, _, _, _) -> (print_endline "Internal error! unexpected value"; assert false;)
  in
  List.fold_right (fun conf rest -> cases_of_c1 conf rest) c1_confs []

type config_kind = Opponent | Proponent

(*** FUNCTIONS TO START THE GAME ***)
(* USING MUTABLE STACK/QUEUE *)
let print_success_message init_bound =
  Printf.printf
    "END! Nothing more to explore; no difference was found between the terms with bound = %d. "
    init_bound;
  (if !bound_reached
   then
     begin
       begin
         if !twice_twice
         then print_endline "Could not prove the counterexample found with generalisations on is real. Please try again with a bigger bound, or update the generalisation."
         else print_endline "However the bound was exceeded in some plays."
       end;
       exit exit_unknown
     end
   else
     begin
       print_endline "The bound was not exceeded - the terms are indeed equivalent!";
       exit exit_eq
     end)

let sprint_names names1 names2 =
  match names1, names2 with
  | Some names1, Some names2 ->
     Printf.sprintf "Names found: \n%s\n%s"
     (Printf.sprintf "C1 Names: \n%s\n" (string_of_conf_names names1))
     (Printf.sprintf "C2 Names: \n%s\n" (string_of_conf_names names2))
  | Some names1, None ->
     Printf.sprintf "Names found: \n%s\n%s"
       (Printf.sprintf "C1 Names: \n%s\n" (string_of_conf_names names1))
       (Printf.sprintf "C2 Names: \nNONE\n")
  | None, Some names2 ->
     Printf.sprintf "Names found: \n%s\n%s"
       (Printf.sprintf "C1 Names: \nNONE\n")
       (Printf.sprintf "C2 Names: \n%s\n" (string_of_conf_names names2))
  | None, None -> "No names found (both are None)"

let debug_id_prints cfg_pair =
  match cfg_pair.c1, cfg_pair.c2 with
  | Some c1, Some c2 ->
     print_debug_id (Printf.sprintf "normalised pair:\n%s" (string_of_cfg_pair cfg_pair));
     print_debug_id (Printf.sprintf "G's equal? %b" ((string_of_g c1.g) = (string_of_g c2.g)));
     print_debug_id (Printf.sprintf "K's equal? %b" (c1.k = c2.k));
     print_debug_id (Printf.sprintf "S's equal? %b" (c1.s = c2.s));
     print_debug_id (Printf.sprintf "E's equal? %b" (c1.e = c2.e))
  | _ -> print_debug_id "id not applicable"

let check_cfg_equality cfg_pair =
  (* TODO: THIS IS HACKY! I don't know why g's are not equal, but their strings are*)
  minimal_of_cfg_opt cfg_pair.c1 = minimal_of_cfg_opt cfg_pair.c2

(* TODO: remove "skip", set variables instead *)
let op_gc_normalisation_memoisation cfg_pair0 memo_cache =
  if not !flag_memo then Some cfg_pair0 else

    (*** REMOVE GAMMA DUPLICATES FIRST ***)
    let cfg_pair0 = gamma_uniq cfg_pair0 in
    
    (*** FIND ALL NAMES ***)
    let nxtid,names_sigma = names_of_sigma (fst cfg_pair0.sigma) (1,NameMap.empty) in
    let names1 = get_conf_names cfg_pair0.c1 nxtid in
    let names2 = get_conf_names cfg_pair0.c2 nxtid in

    (** PRINT **)
    print_debug_norm "===START OF NORMALISATION CYCLE===";
    print_debug_norm (Printf.sprintf "SIGMA names:\n%s\n" (string_of_names_map names_sigma));
    print_debug_norm (sprint_names names1 names2);
    print_debug_norm (Printf.sprintf "configuration before:\n%s\n" (string_of_cfg_pair cfg_pair0));

    (*** GARBAGE COLLECT LOCATIONS ***)
    let cfg_pair1 =
      if not !flag_gc then cfg_pair0 else
        {cfg_pair0 with c1 = garbage_collect_conf cfg_pair0.c1 names1;
                        c2 = garbage_collect_conf cfg_pair0.c2 names2;}
    in

    print_debug_sigma_gc "==START OF SIGMA GC CYCLE==";
    print_debug_sigma_gc (Printf.sprintf "OLD SIGMA:\n%s" (string_of_sigma (fst cfg_pair0.sigma)));
    let garbage_collected_sigma = garbage_collect_sigma cfg_pair0.sigma names1 names2 in
    print_debug_sigma_gc (Printf.sprintf "NEW SIGMA:\n%s" (string_of_sigma (fst garbage_collected_sigma)));

    print_debug_sigma_simp "==START OF SIGMA SIMP CYCLE==";
    print_debug_sigma_simp (Printf.sprintf "OLD SIGMA:\n%s" (string_of_sigma (fst garbage_collected_sigma)));
    let simplified_sigma = simplify_sigma garbage_collected_sigma names1 names2 in
    print_debug_sigma_simp (Printf.sprintf "NEW SIGMA:\n%s" (string_of_sigma (fst simplified_sigma)));
    
    let cfg_pair2 = {cfg_pair1 with sigma = simplified_sigma} in
    
    let nxtid,names_sigma = names_of_sigma (fst cfg_pair2.sigma) (1,NameMap.empty) in
    let names1 = get_conf_names cfg_pair2.c1 nxtid in
    let names2 = get_conf_names cfg_pair2.c2 nxtid in
    
    (*** NORMALISING CONFIG FOR MEMOISATION ***)
    print_debug_sigma_norm "==START OF SIGMA NORM CYCLE==";
    print_debug_sigma_norm (Printf.sprintf "SIGMA FLAG: %b" !flag_sigma_norm);
    print_debug_sigma_norm (Printf.sprintf "OLD SIGMA:\n%s" (string_of_sigma (fst cfg_pair2.sigma)));
    let normalised_sigma =
      if not !flag_sigma_norm then cfg_pair2.sigma else
        normalise_sigma (fst cfg_pair2.sigma) names_sigma , (snd cfg_pair2.sigma)
    in
    print_debug_sigma_norm (Printf.sprintf "NEW SIGMA:\n%s" (string_of_sigma (fst normalised_sigma)));
    let normalised_cfg_pair =
      if not !flag_norm then cfg_pair2 else
        {cfg_pair2 with c1 = normalise_conf cfg_pair2.c1 names1 names_sigma;
                        c2 = normalise_conf cfg_pair2.c2 names2 names_sigma;
                        sigma = normalised_sigma}
    in
    (** PRINT **)
    let names_to_print () =
      let nxtid',names_sigma' = names_of_sigma (fst normalised_cfg_pair.sigma) (1,NameMap.empty) in
      let names1' = get_conf_names normalised_cfg_pair.c1 nxtid' in
      let names2' = get_conf_names normalised_cfg_pair.c2 nxtid' in
      print_debug_sigma_norm (Printf.sprintf "SIGMA names:\n%s\n" (string_of_names_map names_sigma'));
      print_debug_norm (sprint_names names1' names2')
    in
    lazy_print_debug names_to_print debug_norm;
    print_debug_norm (Printf.sprintf "configuration after:\n%s\n" (string_of_cfg_pair normalised_cfg_pair));

    (*** UP-TO IDENTITY ***)
    (*g: g_map; k: typed_eval_cxt list; s: store;*)
    debug_id_prints normalised_cfg_pair;
    if check_cfg_equality normalised_cfg_pair && !flag_id
    then
      begin
        print_debug_id "configuration pruned"; None
      end
    else
      
      (*** ATTEMPT MEMOISATION ***)
      if not (Memoisation.add memo_cache (minimal_of_cfg_pair normalised_cfg_pair))
      then (None) (* memoisation failed, i.e. config already seen *)
      else (Some {cfg_pair1 with sigma = garbage_collected_sigma})


(* PR UP-TO TECHNIQUES *)
let pr_upto_techniques cfg_pair =
  upto_separation cfg_pair

(* BISIM FUNCTIONS *)
let rec play_bisim_game_bfs cfg_pair_lst init_bound max_pending_confs memo_cache =
  print_debug_confs ("No of configs = " ^ (string_of_int (List.length cfg_pair_lst)));
  if (List.length cfg_pair_lst) > max_pending_confs  then
    (print_endline ("!No of configs = " ^ (string_of_int (List.length cfg_pair_lst))); assert false);
  let is_opponent_cfg_pair {c1; c2} =
    match c1, c2 with
    | None, None -> true
    | Some {e=None}, _ -> true
    | _, Some {e=None} -> true
    | _, _ -> false
  in
  let get_next next_cfg_lst cfg_pair =
    (*** this makes the tool not find inequivalences it did before; e.g., ex1v1-ineq.bils ***)
    if min (fst cfg_pair.bound) (snd cfg_pair.bound) <= 0 then begin
        bound_reached := true;
        print_debug_traces (Printf.sprintf "Bound Reached on trace:\n%s" (string_of_trace cfg_pair.tr));
        next_cfg_lst
      end
    else
      (* for performance put the short lists first (1-4 elements); 
         next_cfg_lst can be arbitrarily long (100K elemens) *)
      if is_opponent_cfg_pair cfg_pair
      then (match op_gc_normalisation_memoisation cfg_pair memo_cache with
            | None -> next_cfg_lst
            | Some cfg_pair -> (op_transitions cfg_pair) @ next_cfg_lst)
      else (pr_transitions (pr_upto_techniques cfg_pair)) @ next_cfg_lst
  in
  match cfg_pair_lst with
  | [] -> print_success_message init_bound
  | _  -> play_bisim_game_bfs (List.fold_left get_next [] cfg_pair_lst) init_bound max_pending_confs memo_cache

let rec play_bisim_game_dfs cfg_pair_lst init_bound max_pending_confs memo_cache =
  print_debug_confs ("No of configs = " ^ (string_of_int (List.length cfg_pair_lst)));
  if (List.length cfg_pair_lst) > max_pending_confs  then
    (print_endline ("!No of configs = " ^ (string_of_int (List.length cfg_pair_lst))); assert false);
  let is_opponent_cfg_pair {c1; c2} =
    match c1, c2 with
    | None, None -> true
    | Some {e=None}, _ -> true
    | _, Some {e=None} -> true
    | _, _ -> false
  in
  let get_next cfg_pair =
    (*** this makes the tool not find inequivalences it did before; e.g., ex1v1-ineq.bils ***)
    if min (fst cfg_pair.bound) (snd cfg_pair.bound) <= 0 then begin
        bound_reached := true;
        print_debug_traces (Printf.sprintf "Bound Reached on trace:\n%s" (string_of_trace cfg_pair.tr));
        []
      end
    else
      if is_opponent_cfg_pair cfg_pair then
        (match op_gc_normalisation_memoisation cfg_pair memo_cache with
         | None -> []
         | Some cfg_pair -> op_transitions cfg_pair)
      else
        (pr_transitions (pr_upto_techniques cfg_pair))
  in
  match cfg_pair_lst with
  | [] -> print_success_message init_bound
  | cfgp :: cfgp_rest  -> play_bisim_game_dfs ((get_next cfgp) @ cfgp_rest) init_bound max_pending_confs memo_cache


(* TOP LEVEL FUNCTION *)
let start_bisim_game e1 e2 bound0
      (_,t,c,b,m,n,g,s,r,i,a,l,f,z,u,e) traversal maxpending maxcache
      (fn,fg,fs,fr,fi,fa,fl,ff,fz,fu,fe)=
  debug_traces := t;
  debug_confs := c;
  debug_sigma := b;
  debug_memo := m;
  debug_norm := n;
  debug_gc := g;
  debug_sep := s;
  debug_nr := r;
  debug_id := i;
  debug_sigma_gc := a;
  debug_sigma_norm := l;
  debug_sigma_simp := f;
  debug_generalise := z;
  debug_gamma_duplicates := u;
  debug_reentry := e;
  
  flag_memo := (not (maxcache = 0));
  flag_norm := fn;
  flag_gc := fg;
  flag_sep := fs;
  flag_nr := fr;
  flag_id := fi;
  flag_sigma_gc := fa;
  flag_sigma_norm := fl;  
  flag_sigma_simp := ff;
  flag_generalise := fz;
  flag_gamma_duplicates := fu;
  flag_reentry := fe;
  
  print_debug_traces "TRACES DEBUG: enabled";
  print_debug_confs "CONFIGS DEBUG: enabled";
  print_debug_sigma "SYMBOLIC DEBUG: enabled";
  print_debug_memo "MEMOISATION DEBUG: enabled";
  print_debug_memo (Printf.sprintf "MEMOISATION FLAG: %b" !flag_memo);
  print_debug_norm "NORMALISATION DEBUG: enabled";
  print_debug_norm (Printf.sprintf "NORMALISATION FLAG: %b" !flag_norm);
  print_debug_gc "GARBAGE-COLLECTION DEBUG: enabled";
  print_debug_gc (Printf.sprintf "GARBAGE-COLLECTION FLAG: %b" !flag_gc);
  print_debug_sep "SEPARATION DEBUG: enabled";
  print_debug_sep (Printf.sprintf "SEPARATION FLAG: %b" !flag_sep);
  print_debug_nr "NAME-REUSE DEBUG: enabled";
  print_debug_nr (Printf.sprintf "NAME-REUSE FLAG: %b" !flag_nr);  
  print_debug_sigma_gc "SIGMA-GC DEBUG: enabled";
  print_debug_sigma_gc (Printf.sprintf "SIGMA-GC FLAG: %b" !flag_sigma_gc);
  print_debug_sigma_norm "SIGMA-NORM DEBUG: enabled";
  print_debug_sigma_norm (Printf.sprintf "SIGMA-NORM FLAG: %b" !flag_sigma_norm);
  print_debug_sigma_simp "SIGMA-SIMP DEBUG: enabled";
  print_debug_sigma_simp (Printf.sprintf "SIGMA-SIMP FLAG: %b" !flag_sigma_simp);
  print_debug_generalise "GENERALISATION DEBUG: enabled";
  print_debug_generalise (Printf.sprintf "GENERALISATION FLAG: %b" !flag_generalise);
  print_debug_gamma_duplicates "GAMMA-DUPLICATES DEBUG: enabled";
  print_debug_gamma_duplicates (Printf.sprintf "GAMMA-DUPLICATES FLAG: %b" !flag_gamma_duplicates);
  print_debug_reentry "REENTRY DEBUG: enabled";
  print_debug_reentry (Printf.sprintf "REENTRY FLAG: %b" !flag_reentry);
  
  let start_bisim () = 
    let memo_cache = init_memoisation_cache maxcache in
    let init_cfgp = [{a = empty_abs_set;
                      c1 = Some {g = g_empty ();k = []; s = StoreMap.empty; e = Some {ecxt = []; e = e1}};
                      c2 = Some {g = g_empty ();k = []; s = StoreMap.empty; e = Some {ecxt = []; e = e2}};
                      tr = []; bound = (bound0,bound0); sigma = ([] , (empty_dtree,not fa));
                      ocall_stack = []}]
    in
    if traversal = 0 then
      (play_bisim_game_bfs init_cfgp bound0 maxpending memo_cache) (* BFS *)
    else
      (play_bisim_game_dfs init_cfgp bound0 maxpending memo_cache) (* DFS *)
  in
  retry_fun := start_bisim;
  start_bisim ()

