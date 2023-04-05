open Ast

module StringMap = Map.Make(String)

(* assign_fresh_ids_to_names_XXX (XXX = val/exp)
 *
 * Assigns fresh ids to all *bound* identifiers and locations.
 * Lookup is by name.
 * Assumption: expression is double closed (for identifiers and locations)
 * Uses capture-avoiding substitution.
 * It does not affect abstract values.
 * This is used once after parsing.
 *
 * *)

let rec assign_fresh_ids_to_g_prop env gprop =
  match gprop with
  | GConst _ -> gprop
  | GIdent (id, p) ->
     begin
       match StringMap.find_opt id.str env with
       | None -> raise (Error.SyntaxE (p, "(1) unbound variable: " ^ id.str))
       | Some i -> GIdent ({idid=i; str=id.str}, p)
     end
  | GArith (op, gs, p) ->
     let newgs = List.map (assign_fresh_ids_to_g_prop env) gs in
     GArith (op, newgs, p)
  | GAbsCon _ -> gprop
  | GDeref (l, p) ->
     begin
       match StringMap.find_opt (l.str) env with
       | None -> raise (Error.SyntaxE (p, "unbound location: " ^ l.str))
       | Some i -> GDeref ({locid=i; str=l.str}, p)
     end


let rec assign_fresh_ids_to_names_val env v =
  let refresh_id ({idid; str} as i) = if str = "_" then i else {idid = get_fresh_id (); str = str} in
  let extend str uid env = if str = "_" then env else (StringMap.add str uid env) in
  match v with
  | ConstVal _ -> v
  | TupleVal (vs) -> TupleVal (List.map (assign_fresh_ids_to_names_val env) vs)
  | FunVal (fid, ft, param, pt, e, gen) ->
      let newfid = refresh_id fid in
      let newparam = refresh_id param in
      let newgen =
        match gen with
        | None -> None
        | Some (ws , loc_exp_list , gprop) ->
           let newws = List.map (fun (id,t,m) -> (refresh_id id,t,m)) ws in
           let newenv =
             List.fold_left (fun accenv ({idid; str},_,_) -> extend str idid accenv) env newws
           in
           let newloc_exp_list =
             List.map
               (fun ((l,t),exp) ->
                 let newl =
                   match StringMap.find_opt (l.str) env with
                   | None -> raise (Error.SyntaxE (get_lex_pos exp, "unbound location: " ^ l.str))
                   | Some i -> ({locid=i; str=l.str},t)
                 in
                 let newexp = assign_fresh_ids_to_names_exp newenv exp in
                 (newl,newexp))
               loc_exp_list
           in
           let newgprop = assign_fresh_ids_to_g_prop newenv gprop in
           Some (newws , newloc_exp_list , newgprop)
      in
      let newenv = extend param.str newparam.idid (extend fid.str newfid.idid env) in
      let newe = assign_fresh_ids_to_names_exp newenv e in
      FunVal (newfid, ft, newparam, pt, newe, newgen)
  | AbsCon _ -> v
  | AbsFun (id,t1,t2,s,gen) ->
      let newgen =
        match gen with
        | None -> None
        | Some (ws , loc_exp_list , gprop) ->
           let newws = List.map (fun (id,t,m) -> (refresh_id id,t,m)) ws in
           let newenv =
             List.fold_left (fun accenv ({idid; str},_,_) -> extend str idid accenv) env newws
           in
           let newloc_exp_list =
             List.map
               (fun ((l,t),exp) ->
                 let newl =
                   match StringMap.find_opt (l.str) env with
                   | None -> raise (Error.SyntaxE (get_lex_pos exp, "unbound location: " ^ l.str))
                   | Some i -> ({locid=i; str=l.str},t)
                 in
                 let newexp = assign_fresh_ids_to_names_exp newenv exp in
                 (newl,newexp))
               loc_exp_list
           in
           let newgprop = assign_fresh_ids_to_g_prop newenv gprop in
           Some (newws , newloc_exp_list , newgprop)
      in
      AbsFun (id,t1,t2,s,newgen)
  | ListVal (ls,t) ->
     ListVal (SymList.map (assign_fresh_ids_to_names_val env) (fun x -> x) ls,t)

and assign_fresh_ids_to_names_exp env e =
  let refresh_id ({idid; str} as i) = if str = "_" then i else {idid = get_fresh_id (); str = str} in
  let refresh_loc ({locid; str} as l) = if str = "_" then l else {locid = get_fresh_id (); str = str} in
  let extend str uid env = if str = "_" then env else (StringMap.add str uid env) in
  match e with
  | ValExp (v1, p) -> ValExp (assign_fresh_ids_to_names_val env v1, p)
  | IdentExp  (id, p) ->
     begin
       match StringMap.find_opt id.str env with
       | None ->
          raise (Error.SyntaxE (get_lex_pos e, "unbound variable: " ^ id.str))
       | Some i -> IdentExp ({idid=i; str=id.str}, p)
     end
  | ArithExp (op, es, p) -> 
     let newes =
       List.rev (List.fold_left (fun es e -> (assign_fresh_ids_to_names_exp env e) :: es) [] es) in
     ArithExp (op, newes, p)
  | AppExp (e1, e2, p) ->
     let newe1 = assign_fresh_ids_to_names_exp env e1 in
     let newe2 = assign_fresh_ids_to_names_exp env e2 in
     AppExp (newe1, newe2, p)
  | CondExp (e1, e2, e3, p) ->
     let newe1 = assign_fresh_ids_to_names_exp env e1 in
     let newe2 = assign_fresh_ids_to_names_exp env e2 in
     let newe3 = assign_fresh_ids_to_names_exp env e3 in
     CondExp (newe1, newe2, newe3, p)
  | NewRefExp (l, lt, e1, e2, p) ->
     let newe1 = assign_fresh_ids_to_names_exp env e1 in
     let newl = refresh_loc l in
     let newenv = extend l.str newl.locid env in
     let newe2 = assign_fresh_ids_to_names_exp newenv e2 in
     NewRefExp (newl, lt, newe1, newe2, p)
  | DerefExp  (l, p) -> begin
      match StringMap.find_opt (l.str) env with
      | None -> raise (Error.SyntaxE (get_lex_pos e, "unbound location: " ^ l.str))
      | Some i -> DerefExp ({locid=i; str=l.str}, p)
    end
  | AssignExp (l, e1, p) -> begin
      let newe1 = assign_fresh_ids_to_names_exp env e1 in
      match StringMap.find_opt (l.str) env with
      | None -> raise (Error.SyntaxE (get_lex_pos e, "unbound location: " ^ l.str))
      | Some i -> AssignExp ({locid=i; str=l.str}, newe1, p)
    end
  | LetExp (id, it, e1, e2, p) ->
     let newe1 = assign_fresh_ids_to_names_exp env e1 in
     let newid = refresh_id id in
     let newenv = extend id.str newid.idid env in
     let newe2 = assign_fresh_ids_to_names_exp newenv e2 in
     LetExp (newid, it, newe1, newe2, p)
  | LetTuple (ids_ts, e1, e2, p) ->
     let newe1 = assign_fresh_ids_to_names_exp env e1 in
     let new_ids_ts =
       List.rev (List.fold_left
                   (fun new_ids_ts (i, it) -> (refresh_id i, it) :: new_ids_ts) [] ids_ts) in
     let newenv = List.fold_left (fun env ({idid;str}, it) -> extend str idid env) env new_ids_ts in
     let newe2 = assign_fresh_ids_to_names_exp newenv e2 in
     LetTuple (new_ids_ts, newe1, newe2, p)
  | SeqExp (e1, e2, p) ->
     let newe1 = assign_fresh_ids_to_names_exp env e1 in
     let newe2 = assign_fresh_ids_to_names_exp env e2 in
     SeqExp (newe1, newe2, p)
  | TupleExp (es, p) ->
     let newes =
       List.rev (List.fold_left (fun es e -> (assign_fresh_ids_to_names_exp env e) :: es) [] es) in
     TupleExp (newes, p)
  | BotExp _ -> e
  | TupleProjExp (e1, i, j, p) ->
     let newe1 = assign_fresh_ids_to_names_exp env e1 in
     TupleProjExp (newe1, i, j, p)
  | TupleUpdExp (e1, i, j, e2, p) ->
     let newe1 = assign_fresh_ids_to_names_exp env e1 in
     let newe2 = assign_fresh_ids_to_names_exp env e2 in
     TupleUpdExp (newe1, i, j, newe2, p)
  | MatchExp (t,e1,e2,i1,i2,e3,p) ->
     let newe1 = assign_fresh_ids_to_names_exp env e1 in
     let newe2 = assign_fresh_ids_to_names_exp env e2 in
     let newi1 = refresh_id i1 in
     let newenv1 = extend i1.str newi1.idid env in
     let newi2 = refresh_id i2 in
     let newenv2 = extend i2.str newi2.idid newenv1 in
     let newe3 = assign_fresh_ids_to_names_exp newenv2 e3 in
     MatchExp (t,newe1,newe2,newi1,newi2,newe3,p)

let assign_fresh_ids_to_names_pgm ({e1; e2} as pgm) =
  let newe1 = assign_fresh_ids_to_names_exp StringMap.empty e1 in
  let newe2 = assign_fresh_ids_to_names_exp StringMap.empty e2 in
  {pgm with e1 = newe1; e2 = newe2}


