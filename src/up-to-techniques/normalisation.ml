
open Upto_tools


let rec normalise_exp : Ast.expression -> conf_names -> name_map -> Ast.expression =
  fun exp names sigma_names ->
  let helper x = normalise_exp x names sigma_names in
  let id_get x =
    match get_mapped_id x names with
    | None ->
       Printf.printf "last name set seen:\n%s\n" (string_of_conf_names names);
       failwith (Printf.sprintf "normalise_exp: id <%s> not found" (Ast.string_of_id x))
    | Some id -> id
  in
  let loc_get x = 
    match get_mapped_loc x names with
    | None ->
       begin
         match get_mapped_idloc x names with
         | None ->
            Printf.printf "last name set seen:\n%s\n" (string_of_conf_names names);
            failwith (Printf.sprintf "normalise_exp: loc <%s> not found" (Ast.string_of_loc x))
         | Some loc -> loc
       end
    | Some loc -> loc
  in
  match exp with
  | ValExp    (v, p) -> ValExp (normalise_val v names sigma_names, p)
  | IdentExp  (id, p) -> IdentExp (id_get id, p)
  | ArithExp  (op, es, p) -> ArithExp (op, List.map helper es, p)
  | AppExp    (e1, e2, p) -> AppExp (helper e1, helper e2, p)
  | CondExp   (e1, e2, e3, p) -> CondExp (helper e1, helper e2, helper e3, p)
  | NewRefExp (l, lt, e1, e2, p) -> NewRefExp (loc_get l, lt, helper e1, helper e2, p)
  | DerefExp  (l, p) -> DerefExp (loc_get l, p) 
  | AssignExp (l, e, p) -> AssignExp (loc_get l, helper e, p) 
  | LetExp    (i, it, e1, e2, p) -> LetExp (id_get i, it, helper e1, helper e2, p)
  | LetTuple  (is_ts, e1, e2, p) ->
     LetTuple (List.map (fun(a,b)->(id_get a,b)) is_ts, helper e1, helper e2, p)
  | SeqExp    (e1, e2, p) -> SeqExp (helper e1, helper e2, p)
  | TupleExp  (es, p) -> TupleExp (List.map helper es, p)
  | BotExp    p -> BotExp p
  | TupleProjExp (e1, i, j, p) -> TupleProjExp (helper e1, i, j, p)
  | TupleUpdExp  (e1, i, j, e2, p) -> TupleUpdExp  (helper e1, i, j, helper e2, p)
  and
normalise_val : Ast.value -> conf_names -> name_map -> Ast.value =
  fun v names sigma_names ->
  let helper x = normalise_val x names sigma_names in
  let id_get x =
    match get_mapped_id x names with
    | None ->
       Printf.printf "last name set seen:\n%s\n" (string_of_conf_names names);
       failwith (Printf.sprintf "normalise_val: id <%s> not found" (Ast.string_of_id x))
    | Some id -> id
  in
  let sigma_get x f =
    match get_mapped_sigma x sigma_names with
    | None ->
       begin
         match get_mapped_abs x names with
         | None -> f x (* TODO: I think this is correct ?? *)
         | Some id -> f id
       end
    | Some id -> f id
  in
  match v with
  | ConstVal c -> ConstVal c
  | TupleVal vs -> TupleVal (List.map helper vs)
  | FunVal (fid, ft, param, pt, e, _) ->
     (* TODO: GEN *)
     FunVal (id_get fid, ft, id_get param, pt, normalise_exp e names sigma_names, None)
  | AbsCon (i, t, s) -> sigma_get {idid=i;str=s} (fun {idid;str} -> Ast.AbsCon (idid, t, str))
  | AbsFun (i, t1, t2, s) -> sigma_get {idid=i;str=s} (fun {idid;str} -> Ast.AbsFun (idid, t1, t2, str))

let normalise_cxt : Reductions_ast.eval_cxt -> conf_names -> name_map -> Reductions_ast.eval_cxt =
  fun cxt names sigma_names ->
  let id_get x =
    match get_mapped_id x names with
    | None ->
       Printf.printf "last name set seen:\n%s\n" (string_of_conf_names names);
       failwith (Printf.sprintf "normalise_cxt: id <%s> not found" (Ast.string_of_id x))
    | Some id -> id
  in
  let loc_get x = 
    match get_mapped_loc x names with
    | None ->
       begin
         match get_mapped_idloc x names with
         | None ->
            Printf.printf "last name set seen:\n%s\n" (string_of_conf_names names);
            failwith (Printf.sprintf "normalise_cxt: loc <%s> not found" (Ast.string_of_loc x))
         | Some loc -> loc
       end
    | Some loc -> loc
  in
  let val_normalise x = normalise_val x names sigma_names in
  let exp_normalise x = normalise_exp x names sigma_names in
  let current_frame_locs : Reductions_ast.eval_frame -> Reductions_ast.eval_frame =
    fun eframe ->
    begin
      match eframe with
      | ArithECxt (op, vs, es, p) -> ArithECxt (op, List.map val_normalise vs, List.map exp_normalise es, p)
      | AppOpECxt (e2, p) -> AppOpECxt (exp_normalise e2, p)
      | AppRandECxt (f, p) -> AppRandECxt (val_normalise f, p)
      | NewRefECxt (l, lt, e2, p) -> NewRefECxt (loc_get l, lt, exp_normalise e2, p)
      | AssignECxt (l, p) -> AssignECxt (loc_get l, p)
      | CondECxt (e1, e2, p) -> CondECxt (exp_normalise e1, exp_normalise e2, p)
      | LetECxt (i, it, e2, p) -> LetECxt (id_get i, it, exp_normalise e2, p)
      | LetTupleECxt (is_ts, e2, p) -> LetTupleECxt (List.map (fun(a,b)->id_get a,b) is_ts, e2, p)
      | SeqECxt (e2,p) -> SeqECxt (exp_normalise e2,p)
      | TupleECxt (vs, es, p) -> TupleECxt (List.map val_normalise vs, List.map exp_normalise es, p)
      | TupleProjECxt (i,j,p) -> TupleProjECxt (i,j,p)
      | TupleFstUpdECxt (i,j,e2,p) -> TupleFstUpdECxt (i,j, exp_normalise e2,p)
      | TupleSndUpdECxt (v1,i,j,p) -> TupleSndUpdECxt (val_normalise v1,i,j,p)
    end
  in
  List.map current_frame_locs cxt

let normalise_cek_exp : Reductions_ast.cek_exp -> conf_names -> name_map -> Reductions_ast.cek_exp =
  fun {ecxt;e} names sigma_names ->
    {ecxt = normalise_cxt ecxt names sigma_names; e = normalise_exp e names sigma_names}

let mk_normalised_store : conf_names -> name_map -> Reductions_ast.store -> Reductions_ast.store =
  fun names sigma_names s ->
  List.fold_right
    (fun (n,i) new_store ->
      let old_l = Ast.{locid=n.id;str=n.str} in
      let new_l = Ast.{locid=i;str=loc_name} in
      match Reductions_ast.StoreMap.find_opt old_l s with
      | None -> new_store (* TODO: ignore locs that aren't created yet *)
      | Some v -> Reductions_ast.StoreMap.add new_l (normalise_val v names sigma_names) new_store
    ) (NameMap.bindings names.locs) (Reductions_ast.StoreMap.empty)

let rec normalise_prop : Z3api.prop -> name_map -> Z3api.prop =
  fun prop names ->
  let sigma_get str id =
    let idid = int_of_string id in
    let ident = {Ast.idid;str} in
    match get_mapped_sigma ident names with
    | None ->
       Printf.printf "last name set seen:\n%s\n" (string_of_names_map names);
       failwith (Printf.sprintf "normalise_val: id <%s> not found" (Ast.string_of_id ident))
    | Some {Ast.idid;str} -> idid
  in
  let update_id_on_w s =
    match String.split_on_char '_' s with
    | [str;id] -> Printf.sprintf "%s_%d" str (sigma_get str id)
    | _ -> failwith "normalise_prop: invalid symbol format"
  in
  let helper x = normalise_prop x names in
  match prop with
  | IntProp _ -> prop
  | BoolProp _ -> prop
  | VarIntProp s -> VarIntProp (update_id_on_w s)
  | VarBoolProp s -> VarBoolProp (update_id_on_w s)
  | AndProp ps -> AndProp (List.map helper ps)
  | OrProp  ps -> OrProp (List.map helper ps)
  | NotProp p  -> NotProp (helper p)
  | EqProp  (p1,p2) -> EqProp (helper p1, helper p2)
  | IteProp (p1,p2,p3) -> IteProp (helper p1, helper p2, helper p3)
  | ImpliesProp (p1,p2) -> ImpliesProp (helper p1, helper p2)
  | LtProp (p1,p2) -> LtProp (helper p1, helper p2)
  | LeProp (p1,p2) -> LeProp (helper p1, helper p2)
  | GtProp (p1,p2) -> GtProp (helper p1, helper p2)
  | GeProp (p1,p2) -> GeProp (helper p1, helper p2)
  | AddProp ps -> AddProp (List.map helper ps)
  | MulProp ps -> MulProp (List.map helper ps)
  | SubProp ps -> SubProp (List.map helper ps)
  | DivProp (p1,p2) -> DivProp (helper p1, helper p2)
  | ModProp (p1,p2) -> ModProp (helper p1, helper p2)
  | UminusProp p -> UminusProp (helper p)

let normalise_sigma : Z3api.sigma -> name_map -> Z3api.sigma =
  fun sigma names ->
  let aux : Z3api.sigma_prop -> Z3api.sigma_prop =
    fun sigma_prop ->
    let abs_get x =
      match get_mapped_sigma x names with
      | None ->
         Printf.printf "last name set seen:\n%s\n" (string_of_names_map names);
         failwith (Printf.sprintf "normalise_val: id <%s> not found" (Ast.string_of_id x))
      | Some {Ast.idid;str} -> idid
    in
    let norm_prop x = normalise_prop x names in
    match sigma_prop with
    | TopIntVarConstNeq ((id1 , str1) , int2) ->
       let new_id = abs_get {idid=id1;str=str1} in
       TopIntVarConstNeq ((new_id , str1) , int2)
    | TopBoolVarConstNeq ((id1 , str1) , bool2) ->
       let new_id = abs_get {idid=id1;str=str1} in
       TopBoolVarConstNeq ((new_id , str1) , bool2)
    | TopIntVarNeq ((id1 , str1) , (id2 , str2)) ->
       let new_id1 = abs_get {idid=id1;str=str1} in
       let new_id2 = abs_get {idid=id2;str=str2} in
       TopIntVarNeq ((new_id1 , str1) , (new_id2 , str2))
    | TopBoolVarNeq ((id1 , str1) , (id2 , str2)) ->
       let new_id1 = abs_get {idid=id1;str=str1} in
       let new_id2 = abs_get {idid=id2;str=str2} in
       TopBoolVarNeq ((new_id1 , str1) , (new_id2 , str2))
    | TopIntEq (id , prop) ->
       let new_id = abs_get {idid=id;str=Z3api.default_sname} in
       TopIntEq (new_id , norm_prop prop)
    | TopBoolEq (id , prop) ->
       let new_id = abs_get {idid=id;str=Z3api.default_sname} in
       TopBoolEq (new_id , norm_prop prop)
    | TopBoolVar (id , str) ->
       let new_id = abs_get {idid=id;str=str} in
       TopBoolVar (new_id , str)
    | TopNotBoolVar (id , str) ->
       let new_id = abs_get {idid=id;str=str} in
       TopNotBoolVar (new_id , str)
  in
  List.map aux sigma


(********* GAMMA DUPLICATE REMOVAL ************)

let gama_dup_indices : (int * Ast.value) list -> (int * Ast.value) list ->
                           Reductions_ast.store -> Reductions_ast.store ->
                           IntSet.t =
  fun vs1 vs2 st1 st2 ->
  
  let uniq lst =
    let seen = Hashtbl.create (List.length lst) in
    let rec aux ls acc =
      match ls with
      | [] -> acc
      | ((k1,x1),(k2,x2))::xs ->
         assert(k1=k2);
         let x1',x2' = Substitution.alpha_normalisation_val x1 ,
                       Substitution.alpha_normalisation_val x2
         in
         let x_seen = Hashtbl.mem seen (x1',x2') in
         Hashtbl.replace seen (x1',x2') ();
         if x_seen
         then aux xs acc
         else aux xs (IntSet.add k1 acc)
    in
    aux lst IntSet.empty
  in
  uniq (List.combine vs1 vs2)
