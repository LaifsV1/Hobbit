open Ast

module IntMap = Map.Make(Int)

(* refresh_bound_ids_XXX (XXX = val/exp)
 *
 * Assigns fresh ids to all *bound* identifiers and locations.
 * Lookup is by name.
 * Assumes the the Barendreght principle.
 * It does not affect abstract values or free identifiers/locations.
 * This is used during subtitution to maintain the the Barendreght principle.
 *
 * *)

let rec refresh_bound_ids_gprop_rec map g refresh_id =
  match g with
  | GConst (c,p) -> g
  | GIdent (id,p) ->
     (match IntMap.find_opt id.idid map with
      | None -> raise (Error.RuntimeE (p, "gprop unbound variable: " ^ id.str))
      (* should not happen *)
      | Some i -> GIdent ({idid=i; str=id.str}, p))
  | GArith (op,gs,p) ->
     let newgs = List.map (fun g -> refresh_bound_ids_gprop_rec map g refresh_id) gs in
     GArith (op, newgs, p)
  | GAbsCon _ -> g
  | GDeref (l,p) ->
     (match IntMap.find_opt (l.locid) map with
      | None -> g
      | Some i -> GDeref ({locid=i; str=l.str}, p))

let rec refresh_bound_ids_val_rec map v refresh_id =
  let extend str iold inew env = if str = "_" then env else (IntMap.add iold inew env) in
  match v with
  | ConstVal _ -> v
  | TupleVal vs ->
     (* TODO: BUG? *)
     let newvs =
       List.rev
         (List.fold_left (fun vs v -> (refresh_bound_ids_val_rec map v refresh_id) :: vs) [] vs) in
     TupleVal newvs
  | FunVal (fid, ft, param, pt, e, gen) ->
     (* TODO: GEN *)
     let newfid = refresh_id fid in
     let newparam = refresh_id param in
     let newmap =
       extend param.str param.idid newparam.idid (extend fid.str fid.idid newfid.idid map) in
     let newe = refresh_bound_ids_exp_rec newmap e refresh_id in
     let newgen =
       match gen with
       | None -> None
       | Some (is, loc_exp_list, gprop) ->
          let newis,newmap =
            List.fold_right
              (fun (i,p,m) (newis,newmap) ->
                let newi = refresh_id i in
                (** NOTE: marker stays the same **)
                (newi,p,m)::newis, extend i.str i.idid newi.idid newmap) is ([],map)
          in
          let new_loc_exp_list =
            List.map
              (fun ((l,p),e) ->
                let newl =
                  match IntMap.find_opt (l.locid) map with
                  | None -> l,p
                  | Some i -> {locid=i; str=l.str},p
                in
                (* use newmap cuz it contains ws created in is *)
                let newe = refresh_bound_ids_exp_rec newmap e refresh_id in
                (newl,newe))
              loc_exp_list
          in
          let newgprop = refresh_bound_ids_gprop_rec newmap gprop refresh_id in
          Some (newis, new_loc_exp_list, newgprop)
     in
     FunVal (newfid, ft, newparam, pt, newe, newgen)
  | AbsCon _ -> v
  | AbsFun (id,t1,t2,s,gen) ->
     let newgen =
       match gen with
       | None -> None
       | Some (is, loc_exp_list, gprop) ->
          let newis,newmap =
            List.fold_right
              (fun (i,p,m) (newis,newmap) ->
                let newi = refresh_id i in
                (** NOTE: marker stays the same **)
                (newi,p,m)::newis, extend i.str i.idid newi.idid newmap) is ([],map)
          in
          let new_loc_exp_list =
            List.map
              (fun ((l,p),e) ->
                let newl =
                  match IntMap.find_opt (l.locid) map with
                  | None -> l,p
                  | Some i -> {locid=i; str=l.str},p
                in
                (* use newmap cuz it contains ws created in is *)
                let newe = refresh_bound_ids_exp_rec newmap e refresh_id in
                (newl,newe))
              loc_exp_list
          in
          let newgprop = refresh_bound_ids_gprop_rec newmap gprop refresh_id in
          Some (newis, new_loc_exp_list, newgprop)
     in
     AbsFun (id,t1,t2,s,newgen)
  | ListVal (ls,t) ->
     let newls = (* note: AbsList ID stays the same *)
       SymList.map (fun v -> refresh_bound_ids_val_rec map v refresh_id) (fun x -> x) ls
     in
     ListVal (newls,t) (** TODO: check if correct **)
     

and refresh_bound_ids_exp_rec map e refresh_id =
  let refresh_loc ({locid; str} as l) = if str = "_" then l else {locid = get_fresh_id (); str = str} in
  let extend str iold inew env = if str = "_" then env else (IntMap.add iold inew env) in
  match e with
  | ValExp (v, p) ->
     let newv = refresh_bound_ids_val_rec map v refresh_id in
     ValExp (newv, p)
  | IdentExp  (id, p) -> 
     (match IntMap.find_opt id.idid map with
      | None ->
         raise (Error.RuntimeE (get_lex_pos e, "refresh_exp unbound variable: " ^ id.str))
      (* only happens with new keywords *)
      | Some i -> IdentExp ({idid=i; str=id.str}, p))
  | ArithExp (op, es, p) ->
     let newes = List.map (fun e -> refresh_bound_ids_exp_rec map e refresh_id) es in
     ArithExp (op, newes, p)
  | AppExp (e1, e2, p) ->
     let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
     let newe2 = refresh_bound_ids_exp_rec map e2 refresh_id in
     AppExp (newe1, newe2, p)
  | CondExp (e1, e2, e3, p) ->
     let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
     let newe2 = refresh_bound_ids_exp_rec map e2 refresh_id in
     let newe3 = refresh_bound_ids_exp_rec map e3 refresh_id in
     CondExp (newe1, newe2, newe3, p)
  | NewRefExp (l, lt, e1, e2, p) ->
     let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
     let newl = refresh_loc l in
     let newmap = extend l.str l.locid newl.locid map in
     let newe2 = refresh_bound_ids_exp_rec newmap e2 refresh_id in
     NewRefExp (newl, lt, newe1, newe2, p)
  | DerefExp  (l, p) ->
     (match IntMap.find_opt (l.locid) map with
      | None -> e
      | Some i -> DerefExp ({locid=i; str=l.str}, p))
  | AssignExp (l, e1, p) ->
     (let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
      match IntMap.find_opt (l.locid) map with
      | None ->  AssignExp (l, newe1, p)
      | Some i -> AssignExp ({locid=i; str=l.str}, newe1, p))
  | LetExp (id, it, e1, e2, p) ->
     let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
     let newid = refresh_id id in
     let newmap = extend id.str id.idid newid.idid map in
     let newe2 = refresh_bound_ids_exp_rec newmap e2 refresh_id in
     LetExp (newid, it, newe1, newe2, p)
  | LetTuple (ids_ts, e1, e2, p) ->
     let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
     let new_ids_ts =
       List.rev (List.fold_left
                   (fun new_ids_ts (i, it) -> (refresh_id i, it) :: new_ids_ts) [] ids_ts) in
     let newmap =
       List.fold_left2
         (fun map ({idid = newidid}, _) ({idid;str}, _) ->
           extend str idid newidid map) map new_ids_ts ids_ts in
     let newe2 = refresh_bound_ids_exp_rec newmap e2 refresh_id in
     LetTuple (new_ids_ts, newe1, newe2, p)
  | SeqExp (e1, e2, p) ->
     let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
     let newe2 = refresh_bound_ids_exp_rec map e2 refresh_id in
     SeqExp (newe1, newe2, p)
  | TupleExp (es, p) ->
     let newes =
       List.rev (List.fold_left
                   (fun es e -> (refresh_bound_ids_exp_rec map e refresh_id) :: es) [] es) in
     TupleExp (newes, p)
  | BotExp _ -> e
  | TupleProjExp (e1, i, j, p) -> 
     let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
     TupleProjExp (newe1, i, j, p)
  | TupleUpdExp  (e1, i, j, e2, p) ->
     let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
     let newe2 = refresh_bound_ids_exp_rec map e2 refresh_id in
     TupleUpdExp  (newe1, i, j, newe2, p)
  | MatchExp (t,e1,e2,i1,i2,e3,p) ->
     let newe1 = refresh_bound_ids_exp_rec map e1 refresh_id in
     let newe2 = refresh_bound_ids_exp_rec map e2 refresh_id in
     let newi1 = refresh_id i1 in
     let newmap1 = extend i1.str i1.idid newi1.idid map in
     let newi2 = refresh_id i2 in
     let newmap2 = extend i2.str i2.idid newi2.idid newmap1 in
     let newe3 = refresh_bound_ids_exp_rec newmap2 e3 refresh_id in
     MatchExp (t,newe1,newe2,newi1,newi2,newe3,p)

let refresh_bound_ids_exp e = 
  let refresh_id ({idid; str} as i) = if str = "_" then i else {idid = get_fresh_id (); str = str} in
  refresh_bound_ids_exp_rec IntMap.empty e refresh_id
let refresh_bound_ids_val v =
  let refresh_id ({idid; str} as i) = if str = "_" then i else {idid = get_fresh_id (); str = str} in
  refresh_bound_ids_val_rec IntMap.empty v refresh_id

let alpha_normalisation_exp e =
  let next_fresh_id = ref 0 in
  let get_fresh_id () = let x = !next_fresh_id in next_fresh_id := !next_fresh_id + 1; x in
  let refresh_id ({idid; str} as i) = if str = "_" then i else {idid = get_fresh_id (); str = str} in
  refresh_bound_ids_exp_rec IntMap.empty e refresh_id

let alpha_normalisation_val v =
  let next_fresh_id = ref 0 in
  let get_fresh_id () = let x = !next_fresh_id in next_fresh_id := !next_fresh_id + 1; x in
  let refresh_id ({idid; str} as i) = if str = "_" then i else {idid = get_fresh_id (); str = str} in
  refresh_bound_ids_val_rec IntMap.empty v refresh_id

(* subst_XXX
 *
 * Regular parallel substitution of free identifiers with values (assumed closed)
 * the Barendreght assumption for identifier ids.
 * This assumption is preserved by calling 'refresh_bound_ids' when a substitution is made
 *
 * *)
let rec subst_gprop map g =
  match g with
  | GConst (c,p) -> g
  | GIdent ({idid = id; str = s}, p) ->
     let g_of_v v =
       match v with
       | ConstVal (IntConst  i) -> GConst(IntConst  i,p)
       | ConstVal (BoolConst b) -> GConst(BoolConst b,p)
       | AbsCon (i, t, s, _) -> GAbsCon (i, t, s, p)
       | _ -> raise (Error.RuntimeE (p, "variable is not an Int, Bool or AbsCon: " ^ s))
     in
     begin
       match (IntMap.find_opt id map) with
       | None -> g
       | Some v -> g_of_v (refresh_bound_ids_val v)
     end
  | GArith (op,gs,p) -> GArith (op, (List.map (fun g -> subst_gprop map g) gs), p)
  | GAbsCon _ -> g
  | GDeref _ -> g

let rec subst_val map v =
  match v with
  | ConstVal _ -> v
  | TupleVal vs ->
      TupleVal (List.map (fun v -> subst_val map v) vs)
  | FunVal (fid, ft, param, pt, e, gen) ->
     (* TODO: GEN *)
      assert ((fid.idid = -1 || not (IntMap.mem fid.idid map))
              && (param.idid = -1 || not (IntMap.mem param.idid map)));
      let newgen =
        match gen with
        | None -> None
        | Some (is, loc_exp_list, gprop) ->
           let new_ls = List.map (fun (l,e) -> (l, subst_exp map e)) loc_exp_list in
           Some (is, new_ls, subst_gprop map gprop)
      in
      FunVal (fid, ft, param, pt, subst_exp map e, newgen)
  | AbsCon _ -> v
  | AbsFun (id,t1,t2,s,gen) ->
     let newgen =
       match gen with
       | None -> None
       | Some (is, loc_exp_list, gprop) ->
          let new_ls = List.map (fun (l,e) -> (l, subst_exp map e)) loc_exp_list in
          Some (is, new_ls, subst_gprop map gprop)
     in
     AbsFun (id,t1,t2,s,newgen)
  | ListVal (ls,t) ->
     ListVal (SymList.map (fun v -> subst_val map v) (fun x -> x) ls, t)
 

and subst_exp map e =
  match e with
  | ValExp    (v, p)          -> ValExp    (subst_val map v, p)         
  | IdentExp  ({idid = id; str = _}, p) -> begin
      match (IntMap.find_opt id map) with
      | None -> e
      | Some v -> ValExp (refresh_bound_ids_val v, None)
    end
  | ArithExp (op, eLst, p)   -> ArithExp(op, (List.map (fun e -> subst_exp map e) eLst), p)  
  | AppExp   (e1, e2, p)     -> AppExp ((subst_exp map e1),(subst_exp map e2), p)  
  | CondExp  (e1, e2, e3, p) -> CondExp((subst_exp map e1),(subst_exp map e2), (subst_exp map e3), p)
  | NewRefExp(l, lt, e1, e2, p) -> NewRefExp (l, lt, (subst_exp map e1), (subst_exp map e2), p) 
  | DerefExp (l, p)          -> DerefExp  (l, p)         
  | AssignExp(l, e, p)       -> AssignExp (l, (subst_exp map e), p)      
  | LetExp   (id, it, e1, e2, p) -> 
     assert (id.idid = -1 || not (IntMap.mem id.idid map));
     LetExp    (id, it, (subst_exp map e1), (subst_exp map e2), p)
  | LetTuple (ids_ts, e1, e2, p)-> 
     let _ = List.map (fun ({idid}, _) -> assert ( idid = -1 || not (IntMap.mem idid map))) ids_ts in
     LetTuple(ids_ts, (subst_exp map e1), (subst_exp map e2), p)
  | SeqExp   (e1, e2, p)     -> SeqExp    ((subst_exp map e1), (subst_exp map e2), p)    
  | TupleExp (es, p)         -> TupleExp  (List.map (fun e -> subst_exp map e) es, p)    
  | BotExp   p               -> e
  | TupleProjExp (e1, i, j, p) -> 
     TupleProjExp (subst_exp map e1, i, j, p)
  | TupleUpdExp  (e1, i, j, e2, p) ->
     TupleUpdExp  (subst_exp map e1, i, j, subst_exp map e2, p)
  | MatchExp (t,e1,e2,i1,i2,e3,p) ->
     assert (i1.idid = -1 || i2.idid = -1
             || not (IntMap.mem i1.idid map) || not (IntMap.mem i2.idid map));
     MatchExp (t,(subst_exp map e1),(subst_exp map e2),i1,i2,(subst_exp map e3),p)

let empty = IntMap.empty
let extend {Ast.idid} v subst = IntMap.add idid v subst
let f map e = subst_exp map e

