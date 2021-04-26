open Ast

let debug = ref false

exception Unify of (Lexing.position * Lexing.position) option * Type.t * Type.t * string
exception TError of expression * Type.t * Type.t

(* Type environment: uniqueId -> Type.t option*)
module TypeMap = Map.Make(Int)
type typeenv = Type.t TypeMap.t

let extend uid typ tenv =
  if uid = -1 then tenv (* "_" identifiers have -1 uid *)
  else begin
    assert (not (TypeMap.exists (fun i _ -> i = uid) tenv));
    TypeMap.add uid typ tenv
  end
  
let lookup = TypeMap.find_opt

type norm_mode =
  | Strict
  | Lax
let rec normalise_type mode t =
  match t with
  | Type.UnitT
  | Type.BoolT
  | Type.IntT -> t
  | Type.FunT (ts, t) -> Type.FunT (List.map (normalise_type mode) ts, normalise_type mode t)
  | Type.TupleT ts ->  Type.TupleT (List.map (normalise_type mode) ts)
  | Type.VarT r -> begin
    match !r with
    | None ->  begin
        match mode with
        | Strict -> raise (Error.TypeE (None, "A top-level unification variable cannot be determined; try using the annotation '_type' after the relation symbol."))
        | Lax -> begin
          (if !debug then print_endline "[typing] Uninstantiated inner type; assuming int");
          r := Some Type.IntT;
          Type.IntT
        end
    end
    | Some t ->
        let t' = normalise_type mode t in
        r := Some t';
        t'
  end

let rec normalise_gprop mode g=
  match g with
  | GConst _ -> g
  | GIdent _ -> g
  | GArith (op,gs,p) -> GArith (op, List.map (normalise_gprop mode) gs,p)
  | GAbsCon (i, t, s, p) -> GAbsCon (i, normalise_type mode t, s, p)
  | GDeref _ -> g

let rec normalise_val mode v=
  match v with
  | ConstVal _ -> v
  | TupleVal vs -> TupleVal (List.map (normalise_val mode) vs)
  | FunVal (f, ft, p, pt, e, gen) ->
     let newgen = match gen with
       | None -> None
       | Some (ws, ls, gprop) ->
          let newws = List.map (fun (w,t) -> w,normalise_type mode t) ws in
          let newls = List.map (fun (l,e) -> l,normalise_exp  mode e) ls in
          let newgprop = normalise_gprop mode gprop in
          Some (newws, newls, newgprop)
     in
     FunVal (f, normalise_type mode ft, p, normalise_type mode pt, normalise_exp mode e, newgen)
  | AbsCon (i, t, s) -> AbsCon (i, normalise_type mode t, s)
  | AbsFun (i, t1, t2, s) -> AbsFun (i, normalise_type mode t1, normalise_type mode t2, s)

and normalise_exp mode e =
  match e with
  | ValExp (v, p) -> ValExp (normalise_val mode v, p)
  | IdentExp  _ -> e
  | ArithExp (op, es, p) -> ArithExp (op, List.map (normalise_exp mode) es, p)
  | AppExp (e1, e2, p) -> AppExp (normalise_exp mode e1, normalise_exp mode e2, p)
  | CondExp (e1, e2, e3, p) -> CondExp (normalise_exp mode e1, normalise_exp mode e2, normalise_exp mode e3, p)
  | NewRefExp (l, lt, e1, e2, p) -> NewRefExp (l, normalise_type mode lt, normalise_exp mode e1, normalise_exp mode e2, p)
  | DerefExp  _ -> e
  | AssignExp (l, e, p) -> AssignExp (l, normalise_exp mode e, p)
  | LetExp (i, it, e1, e2, p) -> LetExp (i, normalise_type mode it, normalise_exp mode e1, normalise_exp mode e2, p)
  | LetTuple (is_ts, e1, e2, p) ->
      LetTuple (List.map (fun (i, t) -> (i, normalise_type mode t)) is_ts, normalise_exp mode e1, normalise_exp mode e2, p)
  | SeqExp (e1, e2, p) -> SeqExp (normalise_exp mode e1, normalise_exp mode e2, p)
  | TupleExp (es, p) -> TupleExp (List.map (normalise_exp mode) es, p)
  | BotExp _ -> e
  | TupleProjExp (e1, i, j, p) -> TupleProjExp (normalise_exp mode e1, i, j, p)
  | TupleUpdExp  (e1, i, j, e2, p) ->  TupleUpdExp  (normalise_exp mode e1, i, j, normalise_exp mode e2, p)


let rec tref_in_type r = function
  | Type.UnitT -> false
  | Type.BoolT -> false
  | Type.IntT -> false
  | Type.FunT (ts, t2) -> (List.fold_left (fun b ty -> b || (tref_in_type r ty)) false ts) || (tref_in_type r t2)
  | Type.TupleT tlst -> List.exists (tref_in_type r) tlst
  | Type.VarT tr ->
      if r == tr then true
      else match !tr with
      | None -> false
      | Some t -> tref_in_type r t

let rec unify p t1 t2 =
  match t1, t2 with
  | Type.UnitT, Type.UnitT -> ()
  | Type.BoolT, Type.BoolT -> ()
  | Type.IntT, Type.IntT -> ()
  | Type.FunT(t1s, tr1), Type.FunT(t2s, tr2) -> 
      if (List.length t1s) = (List.length t2s) then begin
        List.iter2 (unify p) t1s t2s;
        unify p tr1 tr2
      end else raise (Unify (p, t1, t2, "Difference in number of function arguments"))
  | Type.TupleT(t1s), Type.TupleT(t2s) ->
      if (List.length t1s) = (List.length t2s) then
        List.iter2 (unify p) t1s t2s
      else raise (Unify (p, t1, t2, "Difference in length of tuples"))
  | Type.VarT(r1), Type.VarT(r2) when r1 == r2 -> ()
  | Type.VarT({ contents = Some(t1') }), _ -> unify p t1' t2
  | _, Type.VarT({ contents = Some(t2') }) -> unify p t1 t2'
  | Type.VarT({ contents = None } as r1), _ ->
      if tref_in_type r1 t2 then raise (Unify(p, t1, t2, "Unsupported recursive types (1)"));
      r1 := Some(t2)
  | _, Type.VarT({ contents = None } as r2) ->
      if tref_in_type r2 t1 then raise (Unify(p, t1, t2, "Unsupported recursive types (2)"));
      r2 := Some(t1)
  | _, _ -> begin
    raise (Unify (p, t1, t2, "Incompatible type structure"))
  end

let op_type = function
  | Negate -> Type.FunT ([Type.IntT], Type.IntT)
  | Add
  | Subtract
  | Multiply
  | Divide 
  | Modulo -> Type.FunT ([Type.IntT; Type.IntT], Type.IntT)
  | And
  | Or
  | Implies -> Type.FunT ([Type.BoolT; Type.BoolT], Type.BoolT) 
  | Not -> Type.FunT ([Type.BoolT], Type.BoolT)
  | Equal 
  | Different 
  | Less 
  | Greater
  | LessEQ
  | GreaterEQ ->
      let ty = Type.gen_type () in          (* polymorphic (in-) equality *)
      Type.FunT ([ty; ty], Type.BoolT)
  | Fst ->
      let ty1 = Type.gen_type () in          (* polymorphic fst/snd *)
      let ty2 = Type.gen_type () in
      let pairt = Type.TupleT [ty1; ty2] in
      Type.FunT ([pairt], ty1)
  | Snd ->
      let ty1 = Type.gen_type () in          (* polymorphic fst/snd *)
      let ty2 = Type.gen_type () in
      let pairt = Type.TupleT [ty1; ty2] in
      Type.FunT ([pairt], ty2)


let rec type_of_gprop tenv g =
  match g with
  | GConst (IntConst _,_) -> Type.IntT
  | GConst (BoolConst _,_) -> Type.BoolT
  | GConst (UnitConst,p) -> raise (Error.TypeE(p, "type_of_gprop: unit should not be in generalisations"))
  | GIdent (id,p) ->
     begin
       match lookup id.idid tenv with
       | None -> raise (Error.TypeE(p, "type_of_gprop: unbound variable: " ^ id.str))
       (* this is checked in ast.ml so it should not be raised here *)
       | Some ty -> ty
     end
  | GArith (op, rands, p) ->
     let ret_ty = Type.gen_type () in
     unify p (op_type op) (Type.FunT (List.map (type_of_gprop tenv) rands, ret_ty));
     ret_ty
  | GAbsCon (uid, t, s, p) -> t
  | GDeref (l, p) ->
     begin
       match lookup l.locid tenv with
       | None -> raise (Error.TypeE(p, "unbound location: " ^ l.str))
       | Some ty -> ty
     end

let rec type_of_val tenv v =
  match v with
  | ConstVal (IntConst _) -> Type.IntT
  | ConstVal (BoolConst _) -> Type.BoolT
  | ConstVal UnitConst -> Type.UnitT
  | TupleVal vs -> Type.TupleT (List.map (type_of_val tenv) vs)
  | FunVal (f, ft, p, pt, e1, gen) ->
     (* TODO: GEN *)
      let fun_t = Type.FunT ([pt], ft) in
      let fun_tvar = Type.gen_type () in
      let new_tenv = extend f.idid fun_tvar (extend p.idid pt tenv) in
      unify None fun_tvar fun_t;
      unify None ft (type_of_exp new_tenv e1);
      begin
        match gen with
        | None -> ()
        | Some (idts , loc_exp_list , g_prop) ->
           let new_tenv =
             List.fold_right
               (fun (i,it) tenv -> extend i.idid it tenv)
               idts tenv
           in
           (List.iter
             (fun ((l,p),exp) ->
               (* make sure l doesn't contain arrow *)
                let loc_type =
                    match lookup l.locid tenv with
                    | None -> raise (Error.TypeE(p, "check_genexpr: unbound location: " ^ l.str))
                    | Some ty -> ty
                in
                let exp_type = type_of_exp new_tenv exp in
                unify p loc_type exp_type)
             loc_exp_list);
           let g_prop_type = type_of_gprop new_tenv g_prop in
           unify (pos_of_g_prop g_prop) Type.BoolT g_prop_type
      end;      
      fun_t
  | AbsCon (uid, t, s) -> t
  | AbsFun (uid, t1, t2, s) -> Type.FunT ([t1], t2)

and type_of_exp tenv e =
try
  match e with
  | ValExp (v, _) -> type_of_val tenv v
  | IdentExp (id, _) ->
     begin
       match lookup id.idid tenv with
       | None -> raise (Error.TypeE(Ast.get_lex_pos e, "type_of_exp: unbound variable: " ^ id.str))
       (* this is checked in ast.ml so it should not be raised here *)
       | Some ty -> ty
     end
  | ArithExp (op, rands, p) ->
      let ret_ty = Type.gen_type () in
      unify p (op_type op) (Type.FunT (List.map (type_of_exp tenv) rands, ret_ty));
      ret_ty
  | AppExp (op, rand, p) ->
      let ret_ty = Type.gen_type () in
      unify p (type_of_exp tenv op) (Type.FunT ([type_of_exp tenv rand], ret_ty));
      ret_ty
  | CondExp (e1, e2, e3, _) ->
      unify (Ast.get_lex_pos e1) Type.BoolT (type_of_exp tenv e1);
      let t2 = (type_of_exp tenv e2) in
      unify (Ast.get_lex_pos e3) t2 (type_of_exp tenv e3);
      t2
  | NewRefExp (l, lt, e1, e2, _) ->
      unify (Ast.get_lex_pos e1) lt (type_of_exp tenv e1);
      type_of_exp (extend l.locid lt tenv) e2
  | DerefExp (l, _) -> begin
    match lookup l.locid tenv with
    | None -> raise (Error.TypeE(Ast.get_lex_pos e, "unbound location: " ^ l.str)) (* this is checked in ast.ml so it should not be raised here *)
    | Some ty -> ty
  end
  | AssignExp (l, e, _) -> begin
    match lookup l.locid tenv with
    | None -> raise (Error.TypeE(Ast.get_lex_pos e, "unbound location: " ^ l.str)) (* this is checked in ast.ml so it should not be raised here *)
    | Some ty -> 
        unify (Ast.get_lex_pos e) ty (type_of_exp tenv e);
        Type.UnitT
  end
  | LetExp (i, it, e1, e2, _) ->
      unify (Ast.get_lex_pos e1) it (type_of_exp tenv e1);
      let new_tenv = extend i.idid it tenv in
      type_of_exp new_tenv e2
  | LetTuple (is_ts, e1, e2, _) ->
      unify (Ast.get_lex_pos e1) (Type.TupleT(List.map snd is_ts)) (type_of_exp tenv e1);
      let new_tenv = List.fold_left (fun new_tenv (i, it) -> extend i.idid it new_tenv) tenv is_ts in
      type_of_exp new_tenv e2
  | SeqExp (e1, e2, _) ->
      unify (Ast.get_lex_pos e1) Type.UnitT (type_of_exp tenv e1);
      type_of_exp tenv e2
  | TupleExp (es, _) ->
      Type.TupleT (List.map (type_of_exp tenv) es)
  | BotExp _ ->
      Type.gen_type ()
  | TupleProjExp (e1, i, j, p) ->
      if i >= j then
        raise (Error.TypeE(Ast.get_lex_pos e, "incorrect tuple projection: projecting element " ^ (string_of_int i) ^ " out of " ^ (string_of_int j)))
      else
        let tylst = (let rec loop j = if j = 0 then [] else (Type.gen_type ()) :: loop (j-1) in loop j) in
        let ty = Type.TupleT tylst in
        let ity = List.nth tylst i in
        unify (Ast.get_lex_pos e1) ty (type_of_exp tenv e1);
        ity
  | TupleUpdExp  (e1, i, j, e2, p) ->
      if i >= j then
        raise (Error.TypeE(Ast.get_lex_pos e, "incorrect tuple update: projecting element " ^ (string_of_int i) ^ " out of " ^ (string_of_int j)))
      else
        let tylst = (let rec loop j = if j = 0 then [] else (Type.gen_type ()) :: loop (j-1) in loop j) in
        let ty = Type.TupleT tylst in
        let ity = List.nth tylst i in
        unify (Ast.get_lex_pos e1) ty (type_of_exp tenv e1);
        unify (Ast.get_lex_pos e2) ity (type_of_exp tenv e2);
        ty


with Unify (p, t1, t2, m) ->
  let p' = match p with None -> Ast.get_lex_pos e | Some _ -> p in
  raise (Error.TypeE(p',
  ("Unification error: " ^ m ^ ". Cannot unify " ^
  (Type.string_of_t (t1)) ^
  " with " ^
  (Type.string_of_t (t2)))))

let type_pgm {e1; e2; rel = (r, ty)} dbg =
  debug := dbg;
  let t1 = type_of_exp TypeMap.empty e1 in
  let t2 = type_of_exp TypeMap.empty e2 in
  (try unify None t1 t2
   with Unify (p, t1, t2, m) ->
    raise (Error.TypeE(p,
      ("Unification error at top level: Cannot unify the top-level types: "
      ^ (Type.string_of_t (t1)) ^
      " with " ^
      (Type.string_of_t (t2)) ^ ". " ^ m
    ))));
  (try unify None t1 ty
   with Unify (p, t1, t2, m) ->
    raise (Error.TypeE(p,
      ("Unification error at top level: Cannot unify the top-level types: "
      ^ (Type.string_of_t (t1)) ^
      " with " ^
      (Type.string_of_t (t2)) ^ ". " ^ m
    ))));
  (try
    let _ = normalise_type Strict ty in ()
  with Error.TypeE (p, m) ->
    raise (Error.TypeE (p, m ^ "\n[t1; t2; t_rel] = [" ^ (Type.string_of_t t1) ^ ";" ^ (Type.string_of_t t2) ^ ";" ^ (Type.string_of_t ty) ^ "]"))
  );
  if !debug then begin
    print_endline "[typing] After typing:";
    print_string ("[t1; t2] = [" ^ (Type.string_of_t t1) ^ "; " ^ (Type.string_of_t t2) ^ "]");
    print_endline (" = [" ^ (Type.string_of_t t1 ^ "; " ^ (Type.string_of_t t2 ^ "]")));
  end;
  {e1 = normalise_exp Lax e1; e2 = normalise_exp Lax e2; rel = (r, ty)}

(* for debugging *)
let rec debug_get_tvars_type = function
  | Type.FunT (ts, t) -> List.fold_left (fun lst t -> (debug_get_tvars_type t) @ lst) (debug_get_tvars_type t) ts
  | Type.TupleT ts -> List.fold_left (fun lst t -> (debug_get_tvars_type t) @ lst) [] ts 
  | Type.VarT r -> r :: (match !r with
    | None -> []
    | Some t -> (debug_get_tvars_type t))
  | _ -> []

and debug_get_tvars_val = function
  | TupleVal vs -> List.fold_left (fun lst v -> (debug_get_tvars_val v) @ lst) [] vs
  | FunVal (f, ft, p, pt, e, gen) ->
     (* TODO: GEN *)
     (debug_get_tvars_type ft) @ (debug_get_tvars_type pt) @ (debug_get_tvars_exp e)
  | AbsCon (i, it, s) -> (debug_get_tvars_type it)
  | AbsFun (f, ft, pt, s) -> (debug_get_tvars_type ft) @ (debug_get_tvars_type pt)
  | _ -> []

and debug_get_tvars_exp = function
  | ValExp    (v, _) -> debug_get_tvars_val v
  | ArithExp  (op, es, _) -> List.fold_left (fun lst e -> (debug_get_tvars_exp e) @ lst) [] es
  | AppExp    (e1, e2, _) -> (debug_get_tvars_exp e1) @ (debug_get_tvars_exp e2)
  | CondExp   (e1, e2, e3, _) -> (debug_get_tvars_exp e1) @ (debug_get_tvars_exp e2) @ (debug_get_tvars_exp e3)
  | NewRefExp (l, lt, e1, e2, _) -> (debug_get_tvars_type lt) @ (debug_get_tvars_exp e1) @ (debug_get_tvars_exp e2)
  | AssignExp (l, e, _) -> (debug_get_tvars_exp e)
  | LetExp    (i, it, e1, e2, _) -> (debug_get_tvars_type it) @ (debug_get_tvars_exp e1) @ (debug_get_tvars_exp e2)
  | LetTuple  (is_ts, e1, e2, _) -> List.fold_left (fun lst (i, it) -> (debug_get_tvars_type it) @ lst)
                                      ((debug_get_tvars_exp e1) @ (debug_get_tvars_exp e2)) is_ts
  | SeqExp    (e1, e2, _) -> (debug_get_tvars_exp e1) @ (debug_get_tvars_exp e2)
  | TupleExp  (es, _) -> List.fold_left (fun lst e -> (debug_get_tvars_exp e) @ lst) [] es
  | _ -> []

