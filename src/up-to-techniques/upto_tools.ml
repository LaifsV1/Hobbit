open Z3api

(********************************************************************
 * This file contains the necessary tools to apply up-to techniques *
 ********************************************************************)

type exp_conf = { e : Ast.expression ; st : Reductions_ast.store }
type val_conf = { v : Ast.value ; st : Reductions_ast.store }
type eval_conf = { ecxt : Reductions_ast.eval_cxt ; st : Reductions_ast.store }
type gprop_conf = { g : Ast.g_prop ; st : Reductions_ast.store }

module IntSet = Set.Make(Int)
module LocSet = Set.Make(Ast.Location)
type name_id = {id : int; str : string}
module NameId = struct
  type t = name_id
  let compare {id=id1; str=str1}
              {id=id2; str=str2} =
    match compare id1 id2 with
    | 0 -> assert(str1=str2); 0
    | c -> c
end
let string_of_name_id {id = i; str = s} = Printf.sprintf "%s_%d" s i
module NameMap = Map.Make(NameId)
type name_map = int NameMap.t

let string_of_intset iset =
  Printf.sprintf "{%s}" (String.concat "," (List.map string_of_int (IntSet.elements iset)))

let intset_of_namemap : name_map -> IntSet.t =
  fun nm ->
  NameMap.fold (fun {id;str} _ intset -> IntSet.add id intset) nm IntSet.empty

let name_mem name name_map =
  match NameMap.find_opt name name_map with
  | None -> false
  | Some _ -> true
let id_mem : Ast.ident -> name_map -> bool =
  fun {idid;str} name_map -> 
  match NameMap.find_opt {id=idid;str=str} name_map with
  | None -> false
  | Some _ -> true
let loc_mem : Ast.loc -> name_map -> bool =
  fun {locid;str} name_map -> 
  match NameMap.find_opt {id=locid;str=str} name_map with
  | None -> false
  | Some _ -> true

type conf_names = { nxtid : int ; vars : name_map ; locs : name_map ; abs : name_map }
let empty_conf_names = { nxtid = 0 ; vars = NameMap.empty ; locs = NameMap.empty ; abs = NameMap.empty }

let var_name = "_vn"
let loc_name = "_ln"
let sig_name = "_wn"

let get_mapped_id : Ast.ident -> conf_names -> Ast.ident option =
  fun ({idid;str}) names -> 
  match NameMap.find_opt {id=idid;str=str} names.vars with
  | None -> None
  | Some id -> Some {idid=id;str=var_name}
let get_mapped_idloc : Ast.loc -> conf_names -> Ast.loc option =
  fun ({locid;str}) names -> 
  match NameMap.find_opt {id=locid;str=str} names.vars with
  | None -> None
  | Some id -> Some {locid=id;str=loc_name}
let get_mapped_loc : Ast.loc -> conf_names -> Ast.loc option =
  fun ({locid;str}) names -> 
  match NameMap.find_opt {id=locid;str=str} names.locs with
  | None -> None
  | Some id -> Some {locid=id;str=loc_name}
let get_mapped_abs : Ast.ident -> conf_names -> Ast.ident option =
  fun ({idid;str}) names -> 
  match NameMap.find_opt {id=idid;str=str} names.abs with
  | None -> None
  | Some id -> Some {idid=id;str=var_name}
let get_mapped_sigma : Ast.ident -> name_map -> Ast.ident option =
  fun ({idid;str}) names -> 
  match NameMap.find_opt {id=idid;str=str} names with
  | None -> None
  | Some id -> Some {idid=id;str=sig_name}

let add_loc : Ast.Location.t -> conf_names -> conf_names =
  fun {locid; str} names ->
  let nxtid = names.nxtid in
  {names with nxtid = nxtid+1 ; locs = NameMap.add {id=locid;str} nxtid names.locs}
let add_var : Ast.ident -> conf_names -> conf_names =
  fun {idid; str} names ->
  if idid < 0 then
    {names with vars = NameMap.add {id=idid;str} idid names.vars}
  else
    let nxtid = names.nxtid in
    {names with nxtid = nxtid+1 ; vars = NameMap.add {id=idid;str} nxtid names.vars}
let add_var_loc : Ast.loc -> conf_names -> conf_names =
  fun {locid; str} names ->
  let nxtid = names.nxtid in
  {names with nxtid = nxtid+1 ; vars = NameMap.add {id=locid;str} nxtid names.vars}
let add_abs : int -> string -> conf_names -> conf_names =
  fun id str names ->
  let nxtid = names.nxtid in
  {names with nxtid = nxtid+1 ; abs = NameMap.add {id=id;str} nxtid names.abs}
let add_sigma : int -> string -> (int * name_map) -> (int * name_map) =
  fun id str (nxtid,names) ->
  if NameMap.mem {id=id;str} names then (nxtid,names)
  else nxtid+1 , NameMap.add {id=id;str} nxtid names


(*** INTERNAL FUNCTIONS TO GET NAMES ***)

let rec names_of_exp : exp_conf -> conf_names -> LocSet.t -> conf_names =
  fun { e = exp ; st = s } acc exclude -> 
  match exp with
  | ValExp    (v, p) -> names_of_val {v=v;st=s} acc exclude
  | IdentExp  (id, p) -> acc
  | ArithExp  (op, es, p) -> List.fold_right (fun e ls -> names_of_exp {e=e;st=s} ls exclude) es acc
  | AppExp    (e1, e2, p) -> names_of_exp {e=e1;st=s} (names_of_exp {e=e2;st=s} acc exclude) exclude
  | CondExp   (e1, e2, e3, p) ->
     names_of_exp {e=e3;st=s}
       (names_of_exp {e=e2;st=s} (names_of_exp {e=e1;st=s} acc exclude) exclude) exclude
  (** LOCATION BINDER **)
  | NewRefExp (l, lt, e1, e2, p) ->
     let acc' = add_var_loc l acc in
     names_of_exp {e=e2;st=s} (names_of_exp {e=e1;st=s} acc' exclude) (LocSet.add l exclude)
  (** INDIRECTION **)
  | DerefExp  (l, p) -> 
     if LocSet.mem l exclude || loc_mem l acc.locs
     then acc
     else
       begin
         match Reductions_ast.store_deref s l with
         | None -> Error.failwith_lex_opt p "locs of exp: tried to deref fresh location"
         | Some v -> names_of_val {v=v;st=s} (add_loc l acc) exclude
       end
  (** LOCATION USE **)
  | AssignExp (l, e, p) ->
     if LocSet.mem l exclude || loc_mem l acc.locs
     then names_of_exp {e=e;st=s} acc exclude
     else
       begin
         match Reductions_ast.store_deref s l with
         | None -> Error.failwith_lex_opt p "locs of exp: tried to deref fresh location"
         | Some v -> names_of_val {v=v;st=s}
                       (names_of_exp {e=e;st=s} (add_loc l acc) exclude) exclude
       end
  (** VAR BINDER **)
  | LetExp    (i, it, e1, e2, p) ->
     let acc' = add_var i acc in
     names_of_exp {e=e2;st=s} (names_of_exp {e=e1;st=s} acc' exclude) exclude
  (** VAR BINDER **)
  | LetTuple  (is_ts, e1, e2, p) ->
     let acc' = List.fold_right (fun (i,it) ns -> add_var i ns) is_ts acc in
     names_of_exp {e=e2;st=s} (names_of_exp {e=e1;st=s} acc' exclude) exclude
  | SeqExp    (e1, e2, p) -> names_of_exp {e=e2;st=s} (names_of_exp {e=e1;st=s} acc exclude) exclude
  | TupleExp  (es, p) -> List.fold_right (fun e ls -> names_of_exp {e=e;st=s} ls exclude) es acc
  | BotExp    p -> acc
  | TupleProjExp (e1,i,j,p) -> names_of_exp {e=e1;st=s} acc exclude
  | TupleUpdExp (e1,i,j,e2,p) -> names_of_exp {e=e2;st=s}
                                   (names_of_exp {e=e1;st=s} acc exclude) exclude
  | MatchExp (t,e1,e2,i1,i2,e3,p) ->
     let acc0 = names_of_exp {e=e1;st=s} acc exclude in
     let acc1 = names_of_exp {e=e2;st=s} acc0 exclude in
     let acc2 = add_var i1 acc1 in
     let acc3 = add_var i2 acc2 in
     names_of_exp {e=e3;st=s} acc3 exclude


and names_of_val : val_conf -> conf_names -> LocSet.t -> conf_names =
  fun {v;st} acc exclude ->
  match v with
  | ConstVal c -> acc
  | TupleVal vs -> List.fold_right (fun v ls -> names_of_val {v=v;st=st} ls exclude) vs acc
  (** VAR BINDER **)    
  | FunVal (fid, ft, param, pt, e, gen) ->
     let acc = add_var fid acc in
     let acc = add_var param acc in
     let acc =
       match gen with
       | None -> acc
       | Some (ws,ls,gprop) ->
          List.fold_right
            (fun ((l,p),_) acc ->
              if LocSet.mem l exclude || loc_mem l acc.locs
              then acc
              else
                begin
                  match Reductions_ast.store_deref st l with
                  | None -> Error.failwith_lex_opt p "locs of gen: tried to deref fresh location"
                  | Some v -> names_of_val {v;st} (add_loc l acc) exclude
                end) ls (names_of_gprop {g=gprop;st} acc exclude)
     in
     (* TODO: GEN *)
     names_of_exp {e=e;st=st} acc exclude
  (** ABS INSTANCE **)
  | AbsCon (i, t, s, _) -> add_abs i s acc (** NOTE: don't need marker because it doesn't change **)
  (** ABS INSTANCE **)
  | AbsFun  (i, t1, t2, s, gen) ->
     let acc =
       match gen with
       | None -> acc
       | Some (ws,ls,gprop) ->
          List.fold_right
            (fun ((l,p),_) acc ->
              if LocSet.mem l exclude || loc_mem l acc.locs
              then acc
              else
                begin
                  match Reductions_ast.store_deref st l with
                  | None -> Error.failwith_lex_opt p "locs of gen: tried to deref fresh location"
                  | Some v -> names_of_val {v;st} (add_loc l acc) exclude
                end) ls (names_of_gprop {g=gprop;st} acc exclude)
     in
     add_abs i s acc
  | ListVal (ls,t) ->
     Ast.SymList.fold_left
       (fun acc v -> names_of_val {v=v;st=st} acc exclude)
       (fun acc -> function None -> acc | Some {idid;str} -> add_abs idid str acc)
       acc ls
       (** TODO: check if right **)

and names_of_gprop : gprop_conf -> conf_names -> LocSet.t -> conf_names =
  fun {g;st} acc exclude ->
  match g with
  | GConst _ -> acc
  | GIdent _ -> acc
  | GArith (op,gs,_) -> List.fold_right (fun g ls -> names_of_gprop {g;st} ls exclude) gs acc
  | GAbsCon (i,t,s,_) -> acc (* TODO: SHOULD WE ADD NAMES IN GPROP? *)
  | GDeref  (l, p) ->
     if LocSet.mem l exclude || loc_mem l acc.locs
     then acc
     else
       begin
         match Reductions_ast.store_deref st l with
         | None -> Error.failwith_lex_opt p "locs of gp: tried to deref fresh location"
         | Some v -> names_of_val {v;st} (add_loc l acc) exclude
       end



let names_of_cxt : eval_conf -> conf_names -> LocSet.t -> conf_names =
  fun { ecxt = cxt ; st = s } acc exclude ->
  let rec traverse_context : Reductions_ast.eval_cxt -> conf_names -> conf_names =
    fun cxt acc ->
    match cxt with
    | [] -> acc
    | eframe :: rest ->
       begin
         let names_of_frame =
           begin
             match eframe with
             | ArithECxt (op, vs, es, p) ->
                List.fold_right (fun e ls -> names_of_exp {e=e;st=s} ls exclude) es
                  (List.fold_right (fun v ls -> names_of_val {v=v;st=s} ls exclude) vs acc)
             | AppOpECxt (e2, p) -> names_of_exp {e=e2;st=s} acc exclude
             | AppRandECxt (f, p) -> names_of_val {v=f;st=s} acc exclude
             | NewRefECxt (l, lt, e2, p) -> names_of_exp {e=e2;st=s} (add_loc l acc) exclude
             | AssignECxt (l, p) -> add_loc l acc
             | CondECxt (e1, e2, p) ->
                names_of_exp {e=e2;st=s} (names_of_exp {e=e1;st=s} acc exclude) exclude
             | LetECxt (i, it, e2, p) ->
                names_of_exp {e=e2;st=s} (add_var i acc) exclude
             | LetTupleECxt (is_ts, e2, p) ->
                let acc' = List.fold_right (fun (i,it) ns -> add_var i ns) is_ts acc in
                names_of_exp {e=e2;st=s} acc' exclude
             | SeqECxt (e2,p) -> names_of_exp {e=e2;st=s} acc exclude
             | TupleECxt (vs, es, p) ->
                List.fold_right (fun e ls -> names_of_exp {e=e;st=s} ls exclude) es 
                  (List.fold_right (fun v ls -> names_of_val {v=v;st=s} ls exclude) vs acc)
              | TupleProjECxt (i,j,p) -> acc
              | TupleFstUpdECxt (i, j, e2, p) -> names_of_exp {e=e2;st=s} acc exclude
              | TupleSndUpdECxt (v1, i, j, p) -> names_of_val {v=v1;st=s} acc exclude
              | MatchECxt (t,e2,i1,i2,e3,p) ->
                 names_of_exp {e=e3;st=s}
                   (names_of_exp {e=e2;st=s} (add_var i1 (add_var i2 acc)) exclude) exclude
           end
         in
         traverse_context rest names_of_frame
       end
  in
  traverse_context cxt acc

let rec names_of_prop : Z3api.prop -> (int * name_map) -> (int * name_map) =
  fun prop acc ->
  let add_abs_of_string str =
    match String.split_on_char '_' str with
    | [s;i] -> add_sigma (int_of_string i) s acc
    | _ -> failwith "names_of_prop: invalid format"
  in
  match prop with
  | IntProp _ -> acc
  | BoolProp _ -> acc
  | VarIntProp s -> add_abs_of_string s
  | VarBoolProp s -> add_abs_of_string s
  | AndProp ps -> List.fold_right (fun p acc -> names_of_prop p acc) ps acc
  | OrProp  ps -> List.fold_right (fun p acc -> names_of_prop p acc) ps acc
  | NotProp p  -> names_of_prop p acc
  | EqProp  (p1,p2) -> (names_of_prop p1 (names_of_prop p2 acc))
  | IteProp (p1,p2,p3) -> (names_of_prop p3 (names_of_prop p2 (names_of_prop p1 acc)))
  | ImpliesProp (p1,p2) -> (names_of_prop p1 (names_of_prop p2 acc))
  | LtProp (p1,p2) -> (names_of_prop p1 (names_of_prop p2 acc))
  | LeProp (p1,p2) -> (names_of_prop p1 (names_of_prop p2 acc))
  | GtProp (p1,p2) -> (names_of_prop p1 (names_of_prop p2 acc))
  | GeProp (p1,p2) -> (names_of_prop p1 (names_of_prop p2 acc))
  | AddProp ps -> List.fold_right (fun p acc -> names_of_prop p acc) ps acc
  | MulProp ps -> List.fold_right (fun p acc -> names_of_prop p acc) ps acc
  | SubProp ps -> List.fold_right (fun p acc -> names_of_prop p acc) ps acc
  | DivProp (p1,p2) -> (names_of_prop p1 (names_of_prop p2 acc))
  | ModProp (p1,p2) -> (names_of_prop p1 (names_of_prop p2 acc))
  | UminusProp p -> names_of_prop p acc

let names_of_sigma : Z3api.sigma -> (int * name_map) -> (int * name_map) =
  fun sigma acc ->
  let aux : Z3api.sigma_prop -> (int * name_map) -> (int * name_map) =
    fun sigma_prop acc ->
    match sigma_prop with
    | TopIntVarConstNeq ((id1 , str1) , int2) -> add_sigma id1 str1 acc
    | TopBoolVarConstNeq ((id1 , str1) , bool2) -> add_sigma id1 str1 acc
    | TopIntVarNeq ((id1 , str1) , (id2 , str2)) -> add_sigma id2 str2 (add_sigma id1 str1 acc)
    | TopBoolVarNeq ((id1 , str1) , (id2 , str2)) -> add_sigma id2 str2 (add_sigma id1 str1 acc)
    | TopIntEq (id , prop) -> add_sigma id Z3api.default_sname (names_of_prop prop acc)
    | TopBoolEq (id , prop) -> add_sigma id Z3api.default_sname (names_of_prop prop acc)
    | TopBoolVar (id , str) -> add_sigma id str acc
    | TopNotBoolVar (id , str) -> add_sigma id str acc
    | False -> acc
  in
  List.fold_right (fun p acc -> aux p acc) sigma acc


(*** API ***)

(*************************
 * NAME COLLECTION TOOLS *
 *************************)

let names_of_expression e st acc = names_of_exp {e;st}    acc LocSet.empty
let names_of_value      v st acc = names_of_val {v;st}    acc LocSet.empty
let names_of_context ecxt st acc = names_of_cxt {ecxt;st} acc LocSet.empty

let names_of_store : Reductions_ast.store -> conf_names -> conf_names =
  fun st acc -> Reductions_ast.fold_store
                  (fun k v acc' -> names_of_val {v=v;st=st} (add_loc k acc') LocSet.empty) st acc


let names_of_cek_exp : Reductions_ast.cek_exp -> Reductions_ast.store -> conf_names -> conf_names =
  fun {ecxt;e} st acc -> names_of_context ecxt st (names_of_expression e st acc)


(**********************
 * GARBAGE COLLECTION *
 **********************)

(* garbage collection *)
(* garbage_collect :
   - arg 1: store to remove locations from
   - arg 2: locations reachable in the rest of the configuration *)
let garbage_collect : Reductions_ast.store -> name_map -> (string -> unit) -> Reductions_ast.store =
  fun st names print ->
  Reductions_ast.StoreMap.filter
    (fun k v ->
      if loc_mem k names
      then (print (Printf.sprintf "Live location <%s>" (Ast.string_of_loc k)); true)
      else (print (Printf.sprintf "Dead location <%s>" (Ast.string_of_loc k)); false)) st

let string_of_names_map vars =
  String.concat "," (List.map (fun (k,v) ->
                         Printf.sprintf "(%s |-> %d)"
                           (string_of_name_id k) v) (NameMap.bindings vars))

let string_of_abs_list abs =
  String.concat "," (List.map (fun (k,v) ->
                         Printf.sprintf "(%s |-> %d)"
                           (string_of_name_id k) v) (NameMap.bindings abs))

let string_of_conf_names { nxtid ; vars ; locs ; abs } =
  Printf.sprintf "Next ID: %d\nVariables: %s\nLocations: %s\nAlphas: %s"
    nxtid
    (string_of_names_map vars)
    (string_of_names_map locs)
    (string_of_abs_list abs)
  

(********************
 * UP-TO SEPARATION *
 ********************)

let locset_of_namemap : name_map -> LocSet.t =
  fun names ->
  NameMap.fold (fun {id;str} _ locset ->
      LocSet.add {locid=id;str=str} locset) names LocSet.empty


(* gets keys to keep from map *)
let rec find_idx_to_keep_1 : (int * LocSet.t) list -> (int * LocSet.t) list
                         -> LocSet.t -> LocSet.t -> IntSet.t -> LocSet.t * LocSet.t * IntSet.t =
  fun g1_locs_list g2_locs_list e1_locs e2_locs acc ->
  match g1_locs_list,g2_locs_list with
  | [] , [] -> e1_locs , e2_locs , acc
  | (k1,vlocs1)::rest1 , (k2,vlocs2)::rest2 ->
     if not(k1 = k2) then failwith "get_separation_keys: g bindings mismatched keys"
     else
       begin
         let inter_locs1 = LocSet.inter e1_locs vlocs1 in
         let inter_locs2 = LocSet.inter e2_locs vlocs2 in

         if LocSet.is_empty inter_locs1 && LocSet.is_empty inter_locs2
         then find_idx_to_keep_1 rest1 rest2 e1_locs e2_locs acc
         else find_idx_to_keep_1 rest1 rest2 (LocSet.union e1_locs vlocs1) (LocSet.union e2_locs vlocs2) (IntSet.add k1 acc)
       end
  | _ -> failwith "get_separation_keys: g bindings of different length"


(* gets keys to keep from map *)
let rec find_idx_to_keep_2 : (int * LocSet.t) list -> (int * LocSet.t) list
                         -> LocSet.t -> LocSet.t -> IntSet.t -> IntSet.t =
  fun g1_locs_list g2_locs_list e1_locs e2_locs acc -> 
  let new_e1_locs , new_e2_locs , new_acc =
    find_idx_to_keep_1 g1_locs_list g2_locs_list e1_locs e2_locs acc
  in

  if IntSet.is_empty (IntSet.diff new_acc acc)
  then acc
  else find_idx_to_keep_2 g1_locs_list g2_locs_list new_e1_locs new_e2_locs new_acc


let find_keys_to_remove : (int * conf_names) list -> (int * conf_names) list
                          -> conf_names -> conf_names -> int list =
  fun g1s g2s e1_ns e2_ns ->
  let g1s' = List.map (fun (a,v) -> a, locset_of_namemap v.locs) g1s in
  let g2s' = List.map (fun (a,v) -> a, locset_of_namemap v.locs) g2s in
  let e1s' = locset_of_namemap e1_ns.locs in
  let e2s' = locset_of_namemap e2_ns.locs in

  let index_set_to_keep = find_idx_to_keep_2 g1s' g2s' e1s' e2s' IntSet.empty in
  let all_keys = List.fold_right (fun (a,v) acc -> IntSet.add a acc) g1s IntSet.empty in
    
  IntSet.elements (IntSet.diff all_keys index_set_to_keep)



(********************
 * UP-TO NAME REUSE *
 ********************)

let is_ho_in_locs : name_map -> Reductions_ast.store -> bool =
  fun locs s ->
  let rec is_ho_in_locs_aux : (name_id * int) list -> bool =
    fun ls ->
    match ls with
    | ({id;str},_) :: ls ->
       begin
         match Reductions_ast.StoreMap.find_opt {locid=id;str=str} s with
         | None -> is_ho_in_locs_aux ls (* TODO: ignore locs that aren't created yet *)
         | Some v -> if Reductions_ast.is_ho_value v
                     then true
                     else is_ho_in_locs_aux ls
       end
    | [] -> false
  in
  is_ho_in_locs_aux (NameMap.bindings locs)


(* use Reductions_ast.is_ho_in_locs, will need new alpha type *)
(* get_reusable_name:
   - input: old indices, indices already used
   - output: next index to reuse and new used indices set  *)
let get_reusable_name : IntSet.t -> IntSet.t -> (int * IntSet.t) option =
  fun all_ids used_ids ->
  match IntSet.min_elt_opt (IntSet.diff all_ids used_ids) with
  | None -> None
  | Some next_available -> Some (next_available ,
                                 IntSet.add next_available used_ids)
  


(****************************
 * SIGMA GARBAGE COLLECTION *
 ****************************)
(* invariant: every ID points at all its dependencies.
   i.e. no further recursive exploration of all IDs is needed *)

module IdMap = Map.Make(Int)
type dep_tree = (IntSet.t IdMap.t) * bool (* dependency tree * skip *)
let string_of_dtree : dep_tree -> string =
  fun dtree ->
  Printf.sprintf "[%s]"
    (String.concat ";"
       (List.map (fun (k,a) -> Printf.sprintf "(%d , %s)" k (string_of_intset a))
          (IdMap.bindings (fst dtree))))

let empty_dtree = IdMap.empty

let dt_remove_id id (dtree,skip) =
  if skip then (dtree,skip)
  else
  IdMap.remove id dtree , skip

(* union_closure gets the set of all ID's a set of ID points at, plus itself *)
let dt_union_closure : dep_tree -> IntSet.t -> IntSet.t -> IntSet.t =
  fun (dtree,skip) id_set acc ->
  if skip then IntSet.empty
  else
  IntSet.fold
    (fun id acc ->
      IntSet.union
        (match IdMap.find_opt id dtree with
         | None -> IntSet.empty
         | Some ids -> ids)
        acc)
    id_set (* go through ID set *)
    acc (* add whatever ACC you need at the end *)

(* dt_add_id: adds to dtree some new_id and the new_dep_set it depends on, 
   including everything reachable through new_dep_set *)
let dt_add_id : dep_tree -> int -> (int option) list -> dep_tree =
  fun (dtree,skip) new_id new_dep_list ->
  if skip then (dtree,skip)
  else
    let new_dep_set =
      List.fold_right (fun id acc ->
          match id with
          | Some id -> IntSet.add id acc
          | None -> acc) new_dep_list IntSet.empty in
    let dep_closure_set =
      dt_union_closure
        (dtree,skip)
        new_dep_set (* go through dep set *)
        new_dep_set (* add dep set in at the end *)
    in
    IdMap.add new_id dep_closure_set dtree , skip

let dt_add_id_notopt : dep_tree -> int -> int list -> dep_tree =
  fun (dtree,skip) new_id new_dep_list ->
  if skip then (dtree,skip)
  else
    let new_dep_set =
      List.fold_right (fun id acc -> IntSet.add id acc) new_dep_list IntSet.empty in
    let dep_closure_set =
      dt_union_closure
        (dtree,skip)
        new_dep_set (* go through dep set *)
        new_dep_set (* add dep set in at the end *)
    in
    IdMap.add new_id dep_closure_set dtree , skip

let dt_update_id : dep_tree -> int -> (int option) list -> dep_tree =
  fun (dtree,skip) some_id new_dep_list ->
  if skip then (dtree,skip)
  else
    let new_dep_set =
      List.fold_right (fun id acc ->
          match id with
          | Some id -> IntSet.add id acc
          | None -> acc) new_dep_list IntSet.empty in
    let dep_closure_set =
      dt_union_closure
        (dtree,skip)
        new_dep_set (* go through dep set *)
        new_dep_set (* add dep set in at the end *)
    in
    (IdMap.update some_id
       (fun y -> match y with None -> Some dep_closure_set
                            | Some y' -> Some (IntSet.union y' dep_closure_set)) dtree) , skip

(* invariant: sigma is in CNF form. We are deleting only things in ANDs *)
(* names1 = names of C1, names2 = names of C2 *)
let sigma_gc : Z3api.sigma -> dep_tree -> conf_names -> conf_names -> (Z3api.sigma * dep_tree) =
  fun sigma dtree names1 names2 ->

  if snd dtree then sigma, dtree
  else
  
    (* ids in the configuration *)
    (* include ids reachable in the dependency tree from ids in configuration *)
    (* remove from dtree all unused names *)
    let abs_set1 = intset_of_namemap names1.abs in
    let abs_set2 = intset_of_namemap names2.abs in
    let conf_ids = IntSet.union abs_set1 abs_set2 in
    let reachable_ids = dt_union_closure dtree conf_ids conf_ids in
    (*let new_dtree = IdMap.filter (fun key id -> IntSet.mem key reachable_ids) dtree in*)

    let rec delete_from_list : dep_tree -> Z3api.sigma -> Z3api.sigma -> (Z3api.sigma * dep_tree) =
      fun dtree sigma acc ->
      match sigma with
      | [] -> List.rev acc , dtree
      | top_prop :: sigma' ->
         begin
           let keep_if_id id =
             let id_dependencies =
               dt_union_closure dtree (IntSet.singleton id) (IntSet.singleton id)
             in
             if IntSet.mem id reachable_ids ||
                  not(IntSet.is_empty (IntSet.inter reachable_ids id_dependencies))
             then delete_from_list dtree sigma' (top_prop :: acc)
             else delete_from_list (dt_remove_id id dtree) sigma' acc
           in
           match top_prop with
           | TopIntVarConstNeq (iv,i) -> keep_if_id (fst iv)
           | TopBoolVarConstNeq (iv,b) -> keep_if_id (fst iv)
           | TopIntVarNeq (iv1 , iv2) -> keep_if_id (fst iv1)
           | TopBoolVarNeq (iv1 , iv2) -> keep_if_id (fst iv1)
           | TopIntEq (id , prop) -> keep_if_id id 
           | TopBoolEq (id , prop) -> keep_if_id id
           | TopBoolVar (id , str) -> keep_if_id id 
           | TopNotBoolVar (id , str) -> keep_if_id id
           | False -> delete_from_list dtree sigma' acc 
         end
    in
    delete_from_list dtree sigma []



(************************
 * SIGMA SIMPLIFICATION *
 ************************)
let rec prop_subs : string -> string -> Z3api.prop -> Z3api.prop =
  fun old_id new_id prop ->
  let get_s s = if s = old_id then new_id else s in
  match prop with
  | IntProp i      -> prop
  | BoolProp true  -> prop
  | BoolProp false -> prop
  | VarIntProp  s  -> VarIntProp (get_s s)
  | VarBoolProp s  -> VarBoolProp (get_s s)
  | AndProp props  -> AndProp (List.map (prop_subs old_id new_id) props)
  | OrProp  props  -> OrProp (List.map (prop_subs old_id new_id) props)
  | NotProp prop   -> NotProp (prop_subs old_id new_id prop)
  | EqProp (p1,p2) -> EqProp (prop_subs old_id new_id p1,prop_subs old_id new_id p2)
  | IteProp (pb,p1,p2) -> IteProp (prop_subs old_id new_id pb,
                                   prop_subs old_id new_id p1,
                                   prop_subs old_id new_id p2)
  | ImpliesProp (p1,p2) -> ImpliesProp (prop_subs old_id new_id p1,
                                        prop_subs old_id new_id p2)
  | LtProp (p1,p2) -> LtProp (prop_subs old_id new_id p1,prop_subs old_id new_id p2)
  | LeProp (p1,p2) -> LeProp (prop_subs old_id new_id p1,prop_subs old_id new_id p2)
  | GtProp (p1,p2) -> GtProp (prop_subs old_id new_id p1,prop_subs old_id new_id p2)
  | GeProp (p1,p2) -> GeProp (prop_subs old_id new_id p1,prop_subs old_id new_id p2)
  | AddProp props -> AddProp (List.map (prop_subs old_id new_id) props)
  | MulProp props -> MulProp (List.map (prop_subs old_id new_id) props)
  | SubProp props -> SubProp (List.map (prop_subs old_id new_id) props)
  | DivProp (p1,p2) -> DivProp (prop_subs old_id new_id p1,prop_subs old_id new_id p2)
  | ModProp (p1,p2) -> ModProp (prop_subs old_id new_id p1,prop_subs old_id new_id p2)
  | UminusProp p1 -> UminusProp (prop_subs old_id new_id p1)

let rec sigma_subs : int -> int -> Z3api.sigma -> Z3api.sigma =
  fun old_id new_id sigma ->
  let get_id id = if id = old_id then new_id else id in
  let subs_prop prop =
    match prop with
    | TopIntEq (id , prop) ->
       (TopIntEq (get_id id,prop_subs (Z3api.name_of_id old_id) (Z3api.name_of_id new_id) prop))
    | TopBoolEq (id , prop) ->
       (TopBoolEq (get_id id,prop_subs (Z3api.name_of_id old_id) (Z3api.name_of_id new_id) prop))
    | TopBoolVar (id,s) ->
       (TopBoolVar (get_id id, s))
    | TopNotBoolVar (id,s) ->
       (TopNotBoolVar (get_id id, s))
    | TopIntVarConstNeq ((id , str) , i) ->
       (TopIntVarConstNeq ((get_id id , str) , i))
    | TopBoolVarConstNeq ((id , str) , b) ->
       (TopBoolVarConstNeq ((get_id id , str) , b))
    | TopIntVarNeq ((id1 , str1) , (id2 , str2)) ->
       (TopIntVarNeq ((get_id id1 , str1) , (get_id id2 , str2)))
    | TopBoolVarNeq ((id1 , str1) , (id2 , str2)) ->
       (TopBoolVarNeq ((get_id id1 , str1) , (get_id id2 , str2)))
    | False -> False
  in
  List.map subs_prop sigma

let replace_if_equal : Z3api.sigma -> Z3api.sigma_prop -> Z3api.sigma_prop -> IntSet.t
                       -> ((int * string) * (int * string) * bool) =
  fun sigma old_prop new_prop idset ->
  (* assertion: ids won't be misused *)
  if old_prop = new_prop then (-2,"_ERR_"),(-2,"_ERR_"),false else 
  match old_prop , new_prop with

  | TopIntEq (id1 , prop1) , TopIntEq (id2 , prop2) ->
     if prop1 = prop2 then
       begin
         if IntSet.mem id1 idset || IntSet.mem id2 idset then
           (default_pair_of_id id1) , (default_pair_of_id id2) , false
         else
           (default_pair_of_id id1) , (default_pair_of_id id2) , true
       end
     else (default_pair_of_id id1) , (default_pair_of_id id2) , false

  | TopBoolEq (id1 , prop1) , TopBoolEq (id2 , prop2) ->
     if prop1 = prop2 then
       begin
         if IntSet.mem id1 idset || IntSet.mem id2 idset then
           (default_pair_of_id id1) , (default_pair_of_id id2) , false
         else
           (default_pair_of_id id1) , (default_pair_of_id id2) , true
       end
     else (default_pair_of_id id1) , (default_pair_of_id id2) , false

  | TopBoolVar id1 , TopBoolVar id2 ->
     begin
       if IntSet.mem (fst id1) idset || IntSet.mem (fst id2) idset then
         id1 , id2 , false
       else
         id1 , id2 , true
     end

  | TopNotBoolVar id1 , TopNotBoolVar id2 ->
     begin
       if IntSet.mem (fst id1) idset || IntSet.mem (fst id2) idset then
         id1 , id2 , false
       else
         id1 , id2 , true
     end

  | _ -> (-3,"_ERR2_"),(-3,"_ERR2_"),false (* assertion: ids won't be misused *)

let sigma_simp : (Z3api.sigma * dep_tree) -> conf_names -> conf_names -> (Z3api.sigma * dep_tree) =
  fun (in_sigma,dtree) names1 names2 ->

  (* ids in the configuration *)
  let abs_set1 = intset_of_namemap names1.abs in
  let abs_set2 = intset_of_namemap names2.abs in
  let conf_ids = IntSet.union abs_set1 abs_set2 in
  
  let rec simplify : dep_tree -> Z3api.sigma -> (Z3api.sigma * dep_tree) =
    fun dtree sigma0 ->
    let rec get_clause : Z3api.sigma -> (Z3api.sigma * dep_tree) =
      fun sigma1 ->
      match sigma1 with
      | [] -> sigma0 , dtree (* made it through all sigma0 without updating *)
      | prop1 :: sigma1' ->
         begin
           let rec find_matching : Z3api.sigma -> (Z3api.sigma * dep_tree) =
             fun sigma2 ->
             match sigma2 with
             | [] -> get_clause sigma1' (* made it through all sigma1 without updating *)
             | prop2 :: sigma2' ->
                let id1,id2,succeeded = replace_if_equal sigma0 prop1 prop2 conf_ids in
                if succeeded then
                  let new_dtree = dt_remove_id (fst id2) dtree in
                  let new_sigma = sigma_subs (fst id1) (fst id2) sigma0 in
                  simplify new_dtree new_sigma
                else
                  find_matching sigma2'
           in
           find_matching sigma1'
         end
    in
    get_clause sigma0
  in
  let new_sigma,new_dtree = simplify dtree in_sigma in
  let uniq lst =
    let seen = Hashtbl.create (List.length lst) in
    List.filter (fun x -> let tmp = not (Hashtbl.mem seen x) in
                          Hashtbl.replace seen x ();
                          tmp) lst
  in
  uniq new_sigma , new_dtree


(***********************************************************************************************
 * SIGMA SUB-SET REMOVAL                                                                       *
 * if `sm && Vx1,...,xn. ¬φ` not SAT, then drop `φ`, where `x1,...,xn` not in `sm` but in `φ`. *
 * `φ` is a list of clauses by closure of reachable variables from root.                       *
 * `¬φ` is obtained by negating the root variable `x1`.                                        *
 * Conditions for removal:                                                                     *
 *  - Only if x1...xn not used in configuration.                                               *
 *  - Only if x1...xn not in RHS of clauses in `sm`.                                           *
 ***********************************************************************************************)
(* input: sigma and the id of a top-level var from which to build phi *)
(* returns ORIGINAL_SIGMA, SIGMA_MINUS, PHI and VAR_SET *)
let build_phi (sigma,dtree) top_id =
  let id_set = (IntSet.singleton top_id) in
  let reachable_ids = dt_union_closure dtree id_set id_set in
  (* checks if a clause involves a reachable id in the LHS *)
  let is_reachable_clause prop =
    match prop with
    | TopIntEq (id , _)
      | TopBoolEq (id , _)
      | TopBoolVar (id, _)
      | TopNotBoolVar (id, _)
      | TopIntVarConstNeq ((id , _) , _)
      | TopBoolVarConstNeq ((id , _) , _) ->
       IntSet.mem id reachable_ids
    | TopIntVarNeq ((id1 , _) , (id2 , _))
      | TopBoolVarNeq ((id1 , _) , (id2 , _)) ->
       (IntSet.mem id1 reachable_ids) || (IntSet.mem id2 reachable_ids)
    | False -> false
  in
  let phi,sigma_minus = List.partition is_reachable_clause sigma in
  (sigma,dtree) , sigma_minus , phi , reachable_ids

(* returns NEW_SIGMA: either sigma_minus or original sigma depending on success *)
let phi_removal conf_ids ((sigma,dtree),sigma_minus,phi,vars) =
  let sigma_m_prop = prop_of_sigma sigma_minus in
  let phi_var_clauses,phi_rest,phi_vars,phi_ids =
    (* gets top_var clauses, rest of phi, and list of LHS vars, list of LHS ids *)
    let aux (top_vars,phi_rest,lhs_vars,lhs_ids) prop = 
      match prop with
      | TopIntEq (id , p) ->
         (top_vars,prop::phi_rest,(sint_of_id id)::lhs_vars,IntSet.add id lhs_ids)
      | TopBoolEq (id , p) ->
         (top_vars,prop::phi_rest,(sbool_of_id id)::lhs_vars,IntSet.add id lhs_ids)
      | TopBoolVar iv ->
         (prop::top_vars,phi_rest,(sbool_of_id_var iv)::lhs_vars,IntSet.add (fst iv) lhs_ids)
      | TopNotBoolVar iv ->
         (top_vars,prop::phi_rest,(sbool_of_id_var iv)::lhs_vars,IntSet.add (fst iv) lhs_ids)
      | TopIntVarConstNeq (iv , i) ->
         (top_vars,prop::phi_rest,(sint_of_id_var iv)::lhs_vars,IntSet.add (fst iv) lhs_ids)
      | TopBoolVarConstNeq (iv , b) ->
         (top_vars,prop::phi_rest,(sbool_of_id_var iv)::lhs_vars,IntSet.add (fst iv) lhs_ids)
      | TopIntVarNeq (iv1 , iv2) ->
         (top_vars,prop::phi_rest,(sint_of_id_var iv2)::(sint_of_id_var iv1)::lhs_vars,
          IntSet.add (fst iv2) (IntSet.add (fst iv1) lhs_ids))
      | TopBoolVarNeq (iv1 , iv2) ->
         (top_vars,prop::phi_rest,(sbool_of_id_var iv2)::(sbool_of_id_var iv1)::lhs_vars,
          IntSet.add (fst iv2) (IntSet.add (fst iv1) lhs_ids))
      | False -> (top_vars,phi_rest,lhs_vars,lhs_ids)
    in
    List.fold_left aux ([],[],[],IntSet.empty) phi
  in
  let phi_vars_uniq = List.sort_uniq compare phi_vars in
  let phi_var_prop = prop_of_sigma phi_var_clauses in
  let phi_rest_prop = prop_of_sigma phi_rest in
  let not_phi_prop = (~~. phi_var_prop) &&. phi_rest_prop in
  let not_phi_z3 = z3_of_prop not_phi_prop in
  let sigma_m_z3 = z3_of_prop sigma_m_prop in
  let vars_z3 = List.map z3_of_prop phi_vars_uniq in
  let forall_not_phi_z3 = forall_z3 vars_z3 not_phi_z3 in
  let sm_and_forall_not_phi_z3 = and_z3 [sigma_m_z3;forall_not_phi_z3] in
  (* REMOVAL CONDITION: LHS not in conf, LHS not in sigma_m *)
  (* note: don't need to check that LHS is not in sigma_m because we partition on reachable ids *)
  let not_in_conf = IntSet.is_empty (IntSet.inter conf_ids phi_ids) in
  if not(check [sm_and_forall_not_phi_z3]) && not_in_conf
  then
    (* assertion: ids in all_vars = ids in input vars *)
    let new_dtree =
      List.fold_left (fun dtree id -> dt_remove_id id dtree) dtree (IntSet.elements vars)
    in
    sigma_minus , new_dtree
  else
    sigma , dtree

(* tries to fold build_phi and phi_removal over all top-level vars, accumulating sigma *)
let sigma_subset_removal (sigma,dtree) names1 names2 =
    
  (* all names in the configuration *)
  let abs_set1 = intset_of_namemap names1.abs in
  let abs_set2 = intset_of_namemap names2.abs in
  let conf_ids = IntSet.union abs_set1 abs_set2 in
  
  (* 0: list all top-level vars in sigma. *)
  let top_level_ids =
    (* gets top_var clauses, rest of phi, and list of all vars *)
    let aux ids prop = 
      match prop with
      | TopIntEq (id , _)
        | TopBoolEq (id , _)
        | TopBoolVar (id, _)
        | TopNotBoolVar (id, _)
        | TopIntVarConstNeq ((id , _) , _)
        | TopBoolVarConstNeq ((id , _) , _) -> IntSet.add id ids
      | TopIntVarNeq ((id1 , _) , (id2 , _))
        | TopBoolVarNeq ((id1 , _) , (id2 , _)) -> IntSet.add id2 (IntSet.add id1 ids)
      | False -> ids
    in
    List.fold_left aux IntSet.empty sigma
  in
  
  (* 1: pop first top-level var, try to build PHI and sigma_minus *)
  (* 2: try to remove PHI and return new sigma' *)
  (* 3: repeat (1) with sigma' until no more top-level vars are left *)
  let new_sigma =
    List.fold_left
      (fun sigma_acc id -> (phi_removal conf_ids) (build_phi sigma_acc id))
      (sigma,dtree)
      (IntSet.elements top_level_ids)
  in
  new_sigma
  
(**************
 * STACKLESS  *
 **************)

(* have a list of pairs (E,b) *)

(* function: traverse list, find first occurrence of b and returns (E,b) *)

(* call: attempt to add (E,b) in front of list. 
         if (E,b) already present:
            TODO: decide
            1. skip call
            2. K::(E,b)::K' => (E,b)::K'
         else:
            K => (E,b)::K *)

(* return: when returning from a (E,b), we add two configurations
           1. one continuing from E
           2. one continuing from the configuration stored in b *)
