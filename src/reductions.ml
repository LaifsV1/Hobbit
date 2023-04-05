open Ast
open Z3api
open Reductions_ast
open Error

(** Main types in this file:
  *
  * store = map Location.t -> value
  * eval_frame : evaluation context frame
  * eval_cxt = eval_frame list : evaluation context
  *
  * type cek_exp = {ecxt: eval_cxt; e: expression}
  * type red_conf = {s:store; e: cek_exp}
  *
  * Main functions in this file:
  * small_step cfg0 bound0: performs a single small step
  * evaluate cfg0 bound0: performs as many as possible small steps
  *
  * ** Invariants
  * * Barendreght convention:
      bound and free identifiers have an int id.
      This is assumed to obey the Barendreght principle:
  * * - bound and free id's are pairwise distinct
  * * - each bound id is distinct from any other bound id
  * * ** This invariant must be maintained by substitution
  * * Similarly for locations
  * 
  * *)



(* for printing purposes *)
let rec unfocus {ecxt; e} =
  match ecxt with
  | [] -> e
  | eframe :: ecxt_rest -> begin
    let new_e =
      match eframe with
      | ArithECxt (op, vs, es, p) -> ArithExp (op, (List.map (fun v -> ValExp (v, None)) vs) @ (e :: es), p) 
      | AppOpECxt (e2, p) -> AppExp (e, e2, p)
      | AppRandECxt (f, p) -> AppExp (ValExp (f, None), e, p)
      | NewRefECxt (l, lt, e2, p) -> NewRefExp (l, lt, e, e2, p)
      | AssignECxt (l, p) -> AssignExp (l, e, p)
      | CondECxt (e1, e2, p) -> CondExp (e, e1, e2, p)
      | LetECxt (i, it, e2, p) -> LetExp (i, it, e, e2, p)
      | LetTupleECxt (is_ts, e2, p) -> LetTuple (is_ts, e, e2, p)
      | SeqECxt (e2,p) -> SeqExp (e, e2, p)
      | TupleECxt (vs, es, p) -> TupleExp ((List.map (fun v -> ValExp (v, None)) vs) @ (e :: es), p)

      | TupleProjECxt (i, j, p) -> TupleProjExp (e, i, j, p)
      | TupleFstUpdECxt (i, j, e2, p) -> TupleUpdExp (e, i, j, e2, p)
      | TupleSndUpdECxt (v, i, j, p) ->  TupleUpdExp (ValExp(v, None), i, j, e, p)
      | MatchECxt (t,e2,i1,i2,e3,p) -> MatchExp (t, e, e2, i1, i2, e3, p)
    in
    unfocus {ecxt = ecxt_rest; e = new_e}
  end



(* focus red_conf -> red_conf option
 *
 * this tries to focus the evaluation in the inner-most expression.
 * It returns None if no further focus is possible.
 * Otherwise it returns a more focused configuration.
 *
 * Assumption: expression is closed
 * *)
let focus {s = s0;  e = {ecxt = ecxt0; e = e0}} =
  match e0 with
  | ValExp (v, _) -> None
  | IdentExp (i, p) ->
     raise (Error.RuntimeE (get_lex_pos e0, (Printf.sprintf "Reduced expression should be closed; free variable: %s" (i.str))))
  | ArithExp (op, [], p) -> None
  | ArithExp (op, e1 :: es, p) ->
     Some { s = s0; e = {ecxt = ArithECxt (op, [], es, p) :: ecxt0; e = e1 }}
  | AppExp (e1, e2, p) ->
     Some { s = s0; e = {ecxt = AppOpECxt (e2, p) :: ecxt0; e = e1 }}
  | CondExp (e1, e2, e3, p) ->
     Some { s = s0; e = {ecxt = CondECxt (e2, e3, p) :: ecxt0; e = e1 }}
  | NewRefExp (l, lt, e1, e2, p) ->
     Some { s = s0; e = {ecxt = NewRefECxt (l, lt, e2, p) :: ecxt0; e = e1 }}
  | DerefExp  (l, p ) -> None
  | AssignExp (l, e1, p) ->
     Some { s = s0; e = {ecxt = AssignECxt (l, p) :: ecxt0; e = e1 }}
  | LetExp (i, it, e1, e2, p) ->
     Some { s = s0; e = {ecxt = LetECxt (i, it, e2, p) :: ecxt0; e = e1 }}
  | LetTuple (is_ts, e1, e2, p) ->
     Some { s = s0; e = {ecxt = LetTupleECxt (is_ts, e2, p) :: ecxt0; e = e1 }}
  | SeqExp (e1, e2, p) ->
     Some { s = s0; e = {ecxt = SeqECxt (e2, p) :: ecxt0; e = e1 }}
  | TupleExp (es, p) -> begin
      match es with
      | [] ->
         raise (Error.RuntimeE (get_lex_pos e0, "tuple expression with zero elements"))
      | e1 :: rest ->
         Some { s = s0; e = {ecxt = TupleECxt ([], rest, p) :: ecxt0; e = e1 }}
    end
  | BotExp p -> None
  | TupleProjExp (e1, i, j, p) ->
     Some { s = s0; e = {ecxt = TupleProjECxt (i, j, p) :: ecxt0; e = e1 }}
  | TupleUpdExp (e1, i, j, e2, p) -> 
     Some { s = s0; e = {ecxt = TupleFstUpdECxt (i, j, e2, p) :: ecxt0; e = e1 }}
  | MatchExp (t, e1, e2, i1, i2, e3, p) ->
     Some { s = s0; e = {ecxt = MatchECxt (t, e2, i1, i2, e3, p) :: ecxt0; e = e1 }}

(*** Reduction functions ***
 *
 * top-level functions: 
 * - small_step cfg bound
 * - evaluate cfg bound
 *
 * *)

(** convert constants to prop constants **)
let value_to_prop v =
  match v with
  | ConstVal c ->
     begin
       match c with
       | IntConst i -> _int i , None
       | BoolConst true -> _true , None
       | BoolConst false -> _false , None
       | UnitConst -> failwith "const to prop: Unit should not be symbolic"
     end
  | TupleVal vs -> failwith "const to prop: tuples should not be symbolic"
  | FunVal _ -> failwith "const to prop: lambdas should not be symbolic"
  | AbsCon (id,typ,name,_) ->
     begin
       match typ with
       | BoolT -> _sbool (Printf.sprintf "%s_%d" name id) , Some id
       | IntT -> _sint (Printf.sprintf "%s_%d" name id) , Some id
       | _ -> failwith "const to prop: encountered unexpected type"
     end
  | AbsFun (_,_,_,_,_) -> failwith "const to prop: function alphas should not be symbolic constants"
  | ListVal _ -> failwith "const to prop: we handle Maps directly, not symbolically"


(* reduce arithmetic operators
 * - accepts arith_op, value list, Lexing.position
 * - produces new expression which inherits the file position p
 *
 * SYMBOLIC: assumes correctly-typed expressions.
 * SND SIGMA: keeps track of dependencies. Add to tree whenever an EQ is introduced
 * *)
let reduce_arith op vs p sigma0 default_sname =
  (** NOTE: marker not needed for values introduced by symbolic execution **)
  let fresh_AbsCon typ = let id = get_fresh_id () in AbsCon(id, typ, default_sname, None) , id in
  let symbolic_binop op i1 i2 typ =
    let i3,id3 = fresh_AbsCon typ in
    let w1,id1 = value_to_prop i1 in
    let w2,id2 = value_to_prop i2 in
    let new_prop = (op w1 w2) in
    let new_sigma =
      match typ with
      | BoolT -> sigma_add_beq id3 new_prop (fst sigma0)
      | IntT -> sigma_add_ieq id3 new_prop (fst sigma0)
      | _ -> report_error_lex p "reduce arith: w3 invalid type"
    in
    Some (ValExp (i3, p),
          (new_sigma ,
           let new_dt0 = Upto_tools.dt_add_id (snd sigma0) id3 [id1; id2] in
           let new_dt1 =
             match id1 with
             | None -> new_dt0
             | Some id1 -> Upto_tools.dt_update_id new_dt0 id1 [id2]
           in
           let new_dt2 =
             match id2 with
             | None -> new_dt1
             | Some id2 -> Upto_tools.dt_update_id new_dt0 id2 [id1]
           in
           new_dt2))
  in
  let symbolic_uniop op i0 typ =
    let i1,id1 = fresh_AbsCon typ in
    let w0,id0 = value_to_prop i0 in
    let new_prop = (op w0) in
    let new_sigma =
      match typ with
      | BoolT -> sigma_add_beq id1 new_prop (fst sigma0)
      | IntT -> sigma_add_ieq id1 new_prop (fst sigma0)
      | _ -> report_error_lex p "reduce arith: w3 invalid type"
    in
    Some (ValExp (i1, p), (new_sigma, Upto_tools.dt_add_id (snd sigma0) id1 [id0]))
  in
  let err_msg s vs =
    let msg = Printf.sprintf "error reducing <%s>: %s" s (string_of_list string_of_val vs) in
    report_error_lex p msg
  in
  (* BUGFIX: used to return None instead of failing *)
  match op with
  | Negate ->
     begin
       match vs with
       | (ConstVal (IntConst i)) :: [] -> Some (ValExp (ConstVal (IntConst (-i)), p), sigma0)
       | (AbsCon (id, IntT, name, _) as i0) :: [] -> symbolic_uniop (~-.) i0 IntT
       | _ -> (err_msg "negate" vs)
     end
  | Add ->
     begin
       match vs with
       | (ConstVal (IntConst i)) :: (ConstVal (IntConst j)) :: [] ->
          Some (ValExp (ConstVal (IntConst (i+j)), p), sigma0)
       | (AbsCon (id1, IntT, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( +. ) i1 i2 IntT
       | i1 :: (AbsCon (id2, IntT, name2, _) as i2) :: [] -> symbolic_binop ( +. ) i1 i2 IntT
       | _ -> (err_msg "add" vs)
     end
  | Subtract ->
     begin
       match vs with
       | (ConstVal (IntConst i)) :: (ConstVal (IntConst j)) :: [] ->
          Some (ValExp (ConstVal (IntConst (i-j)), p), sigma0)
       | (AbsCon (id1, IntT, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( -. ) i1 i2 IntT
       | i1 :: (AbsCon (id2, IntT, name2, _) as i2) :: [] -> symbolic_binop ( -. ) i1 i2 IntT
       | _ -> (err_msg "subtract" vs)
     end
  | Multiply ->
     begin
       match vs with
       | (ConstVal (IntConst i)) :: (ConstVal (IntConst j)) :: [] ->
          Some (ValExp (ConstVal (IntConst (i*j)), p), sigma0)
       | (AbsCon (id1, IntT, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( *. ) i1 i2 IntT
       | i1 :: (AbsCon (id2, IntT, name2, _) as i2) :: [] -> symbolic_binop ( *. ) i1 i2 IntT
       | _ -> (err_msg "multiply" vs)
     end
  | Divide ->
     begin
       match vs with
       | (ConstVal (IntConst i)) :: (ConstVal (IntConst j)) :: [] ->
          Some (ValExp (ConstVal (IntConst (i/j)), p), sigma0)
       | (AbsCon (id1, IntT, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( /. ) i1 i2 IntT
       | i1 :: (AbsCon (id2, IntT, name2, _) as i2) :: [] -> symbolic_binop ( /. ) i1 i2 IntT
       | _ -> (err_msg "divide" vs)
     end
  | Modulo ->
     begin
       match vs with
       | (ConstVal (IntConst i)) :: (ConstVal (IntConst j)) :: [] ->
          Some (ValExp (ConstVal (IntConst (i mod j)), p), sigma0)
       | (AbsCon (id1, IntT, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( %. ) i1 i2 IntT
       | i1 :: (AbsCon (id2, IntT, name2, _) as i2) :: [] -> symbolic_binop ( %. ) i1 i2 IntT
       | _ -> (err_msg "modulo" vs)
     end
  | And ->
     begin
       match vs with
       | (ConstVal (BoolConst i)) :: (ConstVal (BoolConst j)) :: [] ->
          Some (ValExp (ConstVal (BoolConst (i && j)), p), sigma0)
       | (AbsCon (id1, BoolT, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( &&. ) i1 i2 BoolT
       | i1 :: (AbsCon (id2, BoolT, name2, _) as i2) :: [] -> symbolic_binop ( &&. ) i1 i2 BoolT
       | _ -> (err_msg "and" vs)
     end
  | Or ->
     begin
       match vs with
       | (ConstVal (BoolConst i)) :: (ConstVal (BoolConst j)) :: [] ->
          Some (ValExp (ConstVal (BoolConst (i || j)), p), sigma0)
       | (AbsCon (id1, BoolT, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( ||. ) i1 i2 BoolT
       | i1 :: (AbsCon (id2, BoolT, name2, _) as i2) :: [] -> symbolic_binop ( ||. ) i1 i2 BoolT
       | _ -> (err_msg "or" vs)
     end
  | Not ->
     begin
       match vs with
       | (ConstVal (BoolConst i))  :: [] -> Some (ValExp (ConstVal (BoolConst (not i)), p), sigma0)
       | (AbsCon (id, BoolT, name, _) as i0) :: [] -> symbolic_uniop (~~.) i0 BoolT
       | _ -> (err_msg "not" vs)
     end
  | Equal ->
     begin
       match vs with
       | (ConstVal (IntConst i)) :: (ConstVal (IntConst j)) :: [] ->
          Some (ValExp (ConstVal (BoolConst (i = j)), p), sigma0)
       | (ConstVal (BoolConst i)) :: (ConstVal (BoolConst j)) :: [] ->
          Some (ValExp (ConstVal (BoolConst (i = j)), p), sigma0)
       | (ConstVal (UnitConst)) :: (ConstVal (UnitConst)) :: [] ->
          Some (ValExp (ConstVal (BoolConst true), p), sigma0)
       | (AbsCon (id1, typ, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( ==. ) i1 i2 BoolT
       | i1 :: (AbsCon (id2, typ, name2, _) as i2) :: [] -> symbolic_binop ( ==. ) i1 i2 BoolT
       | (ListVal (l1,t1)) :: (ListVal (l2,t2)) :: [] ->
          (** NOTE: require the programmer to implement their own List eq.
                    This is effectively "physical" equality. **)
          assert(t1 = t2); 
          report_error_lex p "<eq>: primitive list comparison not supported."
       | _ -> (err_msg "equal" vs)
     end
  | Different ->
     begin
       match vs with
       | (ConstVal (IntConst i)) :: (ConstVal (IntConst j)) :: [] ->
          Some (ValExp (ConstVal (BoolConst (i <> j)), p), sigma0)
       | (ConstVal (BoolConst i)) :: (ConstVal (BoolConst j)) :: [] ->
          Some (ValExp (ConstVal (BoolConst (i <> j)), p), sigma0)
       | (ConstVal (UnitConst)) :: (ConstVal (UnitConst)) :: [] ->
          Some (ValExp (ConstVal (BoolConst false), p), sigma0)
       (* YYTODO: maybe implement better <> *)
       | (AbsCon (id1, typ, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( <>. ) i1 i2 BoolT
       | i1 :: (AbsCon (id2, typ, name2, _) as i2) :: [] -> symbolic_binop ( <>. ) i1 i2 BoolT
       | (ListVal (l1,t1)) :: (ListVal (l2,t2)) :: [] ->
          (** NOTE: require the programmer to implement their own List neq.
                    This is effectively "physical" neq. **)
          assert(t1 = t2);
          report_error_lex p "<neq>: primitive list comparison not supported."
       | _ -> (err_msg "different" vs)
     end
  | Less -> (* BUGFIX: return type used to be Int *)
     begin
       match vs with
       | (ConstVal (IntConst i)) :: (ConstVal (IntConst j)) :: [] ->
          Some (ValExp (ConstVal (BoolConst (i < j)), p), sigma0)
       | (AbsCon (id1, IntT, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( <. ) i1 i2 BoolT
       | i1 :: (AbsCon (id2, IntT, name2, _) as i2) :: [] -> symbolic_binop ( <. ) i1 i2 BoolT
       | _ -> (err_msg "less" vs)
     end
  | Greater -> (* BUGFIX: return type used to be Int *)
     begin
       match vs with
       | (ConstVal (IntConst i)) :: (ConstVal (IntConst j)) :: [] ->
          Some (ValExp (ConstVal (BoolConst (i > j)), p), sigma0)
       | (AbsCon (id1, IntT, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( >. ) i1 i2 BoolT
       | i1 :: (AbsCon (id2, IntT, name2, _) as i2) :: [] -> symbolic_binop ( >. ) i1 i2 BoolT
       | _ -> failwith (err_msg "greater" vs)
     end
  | LessEQ -> (* BUGFIX: return type used to be Int *)
     begin
       match vs with
       | (ConstVal (IntConst i)) :: (ConstVal (IntConst j)) :: [] ->
          Some (ValExp (ConstVal (BoolConst (i <= j)), p), sigma0)
       | (AbsCon (id1, IntT, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( <=. ) i1 i2 BoolT
       | i1 :: (AbsCon (id2, IntT, name2, _) as i2) :: [] -> symbolic_binop ( <=. ) i1 i2 BoolT
       | _ -> (err_msg "less eq" vs)
     end
  | GreaterEQ -> (* BUGFIX: return type used to be Int *)
     begin
       match vs with
       | (ConstVal (IntConst i)) :: (ConstVal (IntConst j)) :: [] ->
          Some (ValExp (ConstVal (BoolConst (i >= j)), p), sigma0)
       | (AbsCon (id1, IntT, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( >=. ) i1 i2 BoolT
       | i1 :: (AbsCon (id2, IntT, name2, _) as i2) :: [] -> symbolic_binop ( >=. ) i1 i2 BoolT
       | _ -> (err_msg "greater eq" vs)
     end
  | Implies ->
     begin
       match vs with
       | (ConstVal (BoolConst i)) :: (ConstVal (BoolConst j)) :: [] ->
          let imp a b = if a then b else true in
          Some (ValExp (ConstVal (BoolConst (imp i j)), p), sigma0)
       | (AbsCon (id1, BoolT, name1, _) as i1) :: i2 :: [] -> symbolic_binop ( =>. ) i1 i2 BoolT
       | i1 :: (AbsCon (id2, BoolT, name2, _) as i2) :: [] -> symbolic_binop ( =>. ) i1 i2 BoolT
       | _ -> (err_msg "and" vs)
     end
  | Fst ->
     begin
       match vs with
       | TupleVal (v1 :: v2 :: []) :: [] -> Some (ValExp (v1, p), sigma0)
       | _ -> (err_msg "fst" vs)
     end
  | Snd ->
     begin
       match vs with
       | TupleVal (v1 :: v2 :: []) :: [] -> Some (ValExp (v2, p), sigma0)
       | _ -> (err_msg "snd" vs)
     end
  | ListCons ->
     begin
       match vs with
       | v1 :: ListVal (ls,t) :: [] -> Some (ValExp (ListVal(Cons(v1,ls),t),p), sigma0)
       | _ -> (err_msg "cons" vs)
     end
  | PrintOp ->
     begin
       match vs with
       | v1 :: [] -> print_endline (string_of_val v1);
                     Some (ValExp (ConstVal (UnitConst),p), sigma0)
       | _ -> (err_msg "print" vs)
     end
       
 
(* capture avoiding substitution
 *
 * - accepts in an (open) expression e (inside which substitution will occur), the identifier i (to be substittuted), and value v (to substitute i)
 * - returns an expression e
 *
 * * Assumes the Barendreght principle.
 * * Raises an assertion failure if this assumption is violated.
 *
 * * operation based on identifier ids (not their string names)
 *
 * *)
let beta_subst e i v = Substitution.f (Substitution.extend i v Substitution.empty) e
let multi_beta_subst e is vs =
  assert (List.length is = List.length vs);
  let env = List.fold_left2 (fun env i v -> Substitution.extend i v env) Substitution.empty is vs in
  Substitution.f env e
let multi_beta_subst_gprop g is vs =
  assert (List.length is = List.length vs);
  let env = List.fold_left2 (fun env i v -> Substitution.extend i v env) Substitution.empty is vs in
  Substitution.subst_gprop env g


let reduce_app vop varg bound =
  if bound = 0 then None  (* bound exhausted *)
  else
    match vop with 
    | FunVal (f, ft, i, it, e, _) ->
       (* NOTE: gen not handled  *)
        let new_bound = bound - 1 in (* bound decrement *)
        let e = if i.str = "_" then e else (beta_subst e i varg) in
        let e = if f.str = "_" then e else (beta_subst e f vop) in
        Some (e, new_bound)
    | _ -> None (* stuck *)

(* reduces the inner-most evaluation context
 *
 * reduce cfg bnd
 * - cfg: reduction configuration
 * - bnd: application bound
 *
 * Assumption: (focus cfg bnd) = None
 * ie, no more focus is possible, which means expression is value or bot
 *
 * Returns None when it cannot reduce because:
 * - final value has been reached
 * - reduction is application and bound is 0
 * - stuck due to bad types
 * - expression is bot (divergence)
 *
 * Otherwise it returs a new configuration and bound (and sigma).
 * *)
let reduce {s = s0; e ={ecxt = ecxt0; e = e0}} bound0 sigma0 memo list_subs =
  (* hacky references so we don't have to use monads or pass around stuff for single cases *)
  let working_memo = ref memo in
  (* start of actual reduction code *)
  let ret_confs =
    match e0 with
    | BotExp _ -> None :: []
    | ValExp (v, _) ->
       begin
         match ecxt0 with
         | [] -> None :: []
         | ArithECxt (op, vs, [], p) :: ec_rest ->
            begin
              match reduce_arith op (vs @ [v]) p sigma0 Z3api.default_sname with
              | Some (e_new, sigma11) ->
                 Some ({s = s0; e = {ecxt = ec_rest;e = e_new }}, bound0, sigma11, list_subs) :: []
              | None -> None :: []
            end
         | ArithECxt (op, vs, e1 :: e_rest, p) :: ec_rest ->
            Some ({s = s0; e = {ecxt = (ArithECxt (op, vs @ [v], e_rest, p)) :: ec_rest; e = e1}},
                  bound0, sigma0,list_subs) :: []
         | AppOpECxt (e1, p) :: ec_rest ->
            Some ({s = s0; e = {ecxt = (AppRandECxt (v, p)) :: ec_rest;
                                e = e1}}, bound0, sigma0, list_subs) :: []
         | AppRandECxt (v1, p) :: ec_rest  ->
            begin
              match (reduce_app v1 v bound0) with 
              | None -> None :: []
              | Some (e1, bound1) ->
                 begin
                   let cfg1 = {s = s0; e = {ecxt = ec_rest; e = e1}} in
                   let normalised_exp = Substitution.alpha_normalisation_exp e1 in
                   let cfg1_norm = {cfg1 with e = {cfg1.e with e = normalised_exp}} in
                   if not(RedConfSet.mem cfg1_norm memo)
                   then
                     let new_memo = (RedConfSet.add cfg1_norm memo) in
                     working_memo := new_memo;
                     [ Some (cfg1, bound1, sigma0,list_subs) ]
                   else
                     ( print_endline "Reduction Infinite Loop Detected";
                       [ Some ({cfg1 with e = {cfg1.e with e = BotExp None}},
                               bound1, sigma0, list_subs) ])
                 end
            end
         | NewRefECxt (l, lt, e1, p) :: ec_rest  ->
            Some ({s = (store_update s0 l v);
                   e = {ecxt = ec_rest; e = e1}}, bound0, sigma0,list_subs) :: []
         | AssignECxt (l, p) :: ec_rest  ->
            Some ({s = (store_update s0 l v);
                   e = {ecxt = ec_rest; e = ValExp (ConstVal UnitConst, p)}},
                  bound0, sigma0, list_subs) :: []
         | CondECxt (e1, e2, p) :: ec_rest  ->
            begin
              match v with
              | ConstVal (BoolConst true) ->
                 Some ({s = s0; e = {ecxt = ec_rest; e = e1}}, bound0, sigma0, list_subs) :: []
              | ConstVal (BoolConst false) ->
                 Some ({s = s0; e = {ecxt = ec_rest; e = e2}}, bound0, sigma0, list_subs) :: []
              | AbsCon (id, BoolT, name, _) ->
                 (* BUGFIX: type was wrong *)
                 let sigma1 = sigma_add_var id name (fst sigma0) , snd sigma0 in
                 let sigma2 = sigma_add_not_var id name (fst sigma0) , snd sigma0 in
                 let new_conf e' sigma' =
                   Some ({s = s0; e = {ecxt = ec_rest; e = e'}}, bound0, sigma', list_subs) in
                 
                 (* BUGFIX: fixed check for satisfiability *)
                 let new_conf1 = if check_sat_sigma (fst sigma1)
                                 then (new_conf e1 sigma1) :: [] else [] in
                 let new_conf2 = if check_sat_sigma (fst sigma2)
                                 then (new_conf e2 sigma2) :: [] else [] in
                 (*Printf.printf "length: %d\n" (List.length (new_conf1 @ new_conf2));*)
                 new_conf1 @ new_conf2
              | _ -> failwith "reduce error: unexpected pattern with CondECxt"
            end
         | LetECxt (i, it, e1, p) :: ec_rest  ->
            Some ({s = s0; e = {ecxt = ec_rest; e = (beta_subst e1 i v)}},
                  bound0, sigma0, list_subs) :: []
         | LetTupleECxt (is_ts, e1, p) :: ec_rest  ->
            begin
              match v with
              | TupleVal vs ->
                 if (List.length is_ts <> List.length vs) then None :: []
                 else Some ({s = s0; e = {ecxt = ec_rest;
                                          e = (multi_beta_subst e1 (fst (List.split is_ts)) vs)}},
                            bound0, sigma0, list_subs) :: []
              | _ -> None :: []
            end
         | SeqECxt (e1, p) :: ec_rest  ->
            Some ({s = s0; e = {ecxt = ec_rest; e = e1}}, bound0, sigma0, list_subs) :: []
         | TupleECxt (vs, [], p) :: ec_rest ->
            Some ({s = s0; e = {ecxt = ec_rest; e = ValExp (TupleVal (vs @ [v]), p)}},
                  bound0, sigma0, list_subs) :: []
         | TupleECxt (vs, e1 :: e_rest, p) :: ec_rest ->
            Some ({s = s0; e = {ecxt = (TupleECxt (vs @ [v], e_rest, p)) :: ec_rest; e = e1}},
                  bound0, sigma0, list_subs) :: []
         | TupleProjECxt (i, j, p) :: ec_rest ->
            begin
              match v with
              | TupleVal vs ->
                 Some ({s = s0; e = {ecxt = ec_rest; e = ValExp (List.nth vs i, None) }},
                       bound0, sigma0, list_subs) :: []
              | _ -> failwith "reduce error: unexpected pattern with TupleProjECxt"
            end
         | TupleFstUpdECxt (i, j, e2, p) :: ec_rest ->
            Some ({s = s0; e = {ecxt = (TupleSndUpdECxt (v, i, j, p)) :: ec_rest; e = e2}},
                  bound0, sigma0, list_subs) :: []
         | TupleSndUpdECxt (v1, i, j, p) :: ec_rest ->
            begin
              match v1 with
              | TupleVal vs ->
                 (let newvs = List.mapi (fun ii x -> if ii = i then v else x) vs in
                  Some ({s = s0; e = {ecxt = ec_rest; e = ValExp (TupleVal newvs, None)}},
                        bound0, sigma0, list_subs) :: [])
              | _ -> failwith "reduce error: unexpected pattern with TupleSndUpdECxt"
            end
         | MatchECxt (t',e2,i1,i2,e3,p) :: ec_rest ->
            begin
              match v with
              | ListVal (ls, t) ->
                 if t<>t' then Printf.printf "%s, %s\n" (Type.string_of_t t) (Type.string_of_t t');
                 assert(t = t');
                 let new_conf e' list_subs =
                   Some ({s = s0; e = {ecxt = ec_rest; e = e'}}, bound0, sigma0, list_subs)
                 in
                 begin
                   match ls with
                   | Nil -> (* e already Nil, no need to subs *)
                      [new_conf e2 list_subs] 
                   | Cons(x,xs) -> 
                      [new_conf (beta_subst (beta_subst e3 i1 x) i2 (ListVal(xs,t))) list_subs]
                   | AbsList id ->
                      (** TODO: accumulate new alphas in A **)
                      let fresh_abscon typ =
                        AbsCon(get_fresh_id (), typ, default_sname, None) in
                      let rec absval_of_type typ =
                        match typ with
                        | Type.UnitT | Type.BoolT | Type.IntT -> fresh_abscon typ
                        | Type.FunT (ts,t) -> failwith "absval_of_type: functions not implemented"
                        | Type.TupleT ts -> TupleVal(List.map absval_of_type ts)
                        | Type.ListT t -> ListVal(AbsList {idid=get_fresh_id ();str=default_sname},t)
                        | Type.VarT _ -> failwith "absval_of_type: I don't know what this is for"
                      in
                      (* case where ID is nill *)
                      let nil_case = new_conf (abslist_swap_exp id Nil e2) ((id,Nil) :: list_subs) in
                      (* TODO: just for robustness, apply the new substitution in the list_subs *)
                      (* case where ID is some new list *)
                      let cons_case =
                        let new_i1, new_i2 = absval_of_type t,
                                             AbsList {idid=get_fresh_id ();str=default_sname} in
                        let new_list = (Cons(new_i1, new_i2)) in
                        let e3' = (beta_subst (beta_subst e3 i1 new_i1) i2 (ListVal(new_i2,t))) in
                        let e3'' = (abslist_swap_exp id new_list e3') in
                        new_conf e3'' ((id,new_list) :: list_subs)
                        (* TODO: just for robustness, apply the new substitution in the list_subs *)
                      in
                      nil_case :: cons_case :: []
                 end
              | _ -> failwith (Printf.sprintf "reduce error: %s is not a list" (string_of_val v))
            end
       end
    | DerefExp (l, p) -> 
       begin
         match store_deref s0 l with
         | None -> None :: [] (*TODO for the moment unbound locations get stuck -
                              They should be ruled out by closure check at compile time*)
         | Some v -> Some ({s = s0; e = {ecxt = ecxt0; e = ValExp (v, None)}},
                           bound0, sigma0, list_subs) :: []
       end
    | _ -> raise (Error.RuntimeE
                    (get_lex_pos e0, "Internal Error! function 'reduce' called instead of 'focus'"))
  in ret_confs , !working_memo



(* A single small-step reduction
 * It focuses as much as possible and then attempts to take a single reduction
 *
 * Accepts configuration cfg0 and bound0 (and sigma0)
 * Returns:
 * - None: if reduction cannot be performed
 * - Some (cfg, bound, sigma): otherwise
 *
 * Note: focus moves are lost on the stuck terms
 *
 * *)
let rec small_step cfg0 bound0 sigma0 =
  match focus cfg0 with
  | None -> reduce cfg0 bound0 sigma0
  | Some cfg1 -> small_step cfg1 bound0 sigma0

(* Big-step evaluation of configuration
 * Reduce as much as possible, up to the bound (accumulates sigma)
 *
 * Accepts configuration cfg and bound (and sigma)
 *
 * Returns:
 * - (new cfg, bound, sigma)
 *
 * Note: the return configuration is "fully focused"
 *
 * *)
let rec big_step_memo cfg0 bound0 sigma0 memo list_subs =
  (match focus cfg0 with
   | None ->
      begin
        let reduced_confs , new_memo = reduce cfg0 bound0 sigma0 memo list_subs in
        let reduce_conf conf = 
          match conf with
          | None -> (cfg0, bound0, sigma0, list_subs) :: []
          (* stuck due to types or bound0 = 0 and an application was not performed *)
          | Some (cfg1, bound1, sigma1, subs1) -> big_step_memo cfg1 bound1 sigma1 new_memo subs1
        in
        List.fold_right (fun conf rest -> reduce_conf conf @ rest) reduced_confs []
      end
   | Some cfg1 -> big_step_memo cfg1 bound0 sigma0 memo list_subs)

let rec big_step cfg0 bound0 sigma0 substs =
  big_step_memo cfg0 bound0 sigma0 (RedConfSet.empty) substs


(* focuses a configuration as much as possible *)
let rec focus_rec cfg0 =
  match focus cfg0 with
  | None -> cfg0
  | Some cfg1 -> cfg1

(*** helper functions ***)
let string_of_red_conf {s; e} =
  "{s = [...]; e = " ^ (string_of_exp (unfocus e)) ^ "}"


