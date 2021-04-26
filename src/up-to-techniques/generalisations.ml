open Ast
open Error
open Reductions_ast
open Reductions
open Z3api

(* Process for Generalisation:
 * 0. subs ws for abs in ls and gprop
 * 1. check that not(sat(sigma && not(cond) && (!x = exp)))
 * 2. x := exp
 * 3. add cond to sigma *)

(* get first order value of expresion *)
let rec fo_val_of_exp e =
  match e with
  | ValExp    (v, p) -> v
  | TupleExp  (es,p) -> TupleVal (List.map fo_val_of_exp es)
  | _ ->  failwith_lex_opt (get_lex_pos e) "(3): expected ground-type value"

(* return: formula *)
let rec get_l_eq_prop (v,p) e sigma =
  let fresh_AbsCon typ = let id = get_fresh_id () in AbsCon(id, typ, default_sname) , id in     
  let symbolic_binop op i1 i2 =
    let i3,id3 = fresh_AbsCon BoolT in
    let w1,id1 = value_to_prop i1 in
    let w2,id2 = value_to_prop i2 in
    let new_prop = (op w1 w2) in
    sigma_add_var id3 default_sname (sigma_add_beq id3 new_prop sigma)
  in
  match v with
  | TupleVal ls1 ->
     begin
     match fo_val_of_exp e with
     | TupleVal ls2 ->
        begin
          match ls1,ls2 with
          | x::xs , y::ys ->
             get_l_eq_prop (TupleVal xs, p) (ValExp (TupleVal ys, get_lex_pos e))
               (symbolic_binop ( ==. ) x y)
          | [], [] -> sigma
          | _ -> failwith_lex_opt p "tuple lengths mismatch"
        end
     | _ -> failwith_lex_opt p "expected tuple"
     end
  | FunVal _ -> failwith_lex_opt p "(1): expected ground-type value"
  | AbsFun _ -> failwith_lex_opt p "(2): expected ground-type value"
  | v1 -> let v2 = fo_val_of_exp e in
          symbolic_binop ( ==. ) v1 v2


let rec gprop_to_prop gprop ids st =
  match gprop with
  | GIdent (i,p) -> failwith_lex_opt p "(3): expected ground-type value"
  | GConst (IntConst  i,p) -> _int i , ids
  | GConst (BoolConst true,p) -> _true , ids
  | GConst (BoolConst false,p) -> _false , ids
  | GConst (UnitConst,p) -> failwith_lex_opt p "(1): expected int or bool, got unit"
  | GDeref (l,p) ->
     begin
       match store_deref st l with
       | None -> failwith_lex_opt p "location unbound"
       | Some v ->
          begin
            match value_to_prop v with
            | vprop , None   -> vprop , ids
            | vprop , Some i -> vprop , i::ids
          end
     end
  | GAbsCon (i,t,s,p) ->
     begin
       match t with
       | Type.BoolT -> _sbool (name_of_iv (i,s)) , i::ids
       | Type.IntT  -> _sint  (name_of_iv (i,s)) , i::ids
       | Type.UnitT -> failwith_lex_opt p "(2): expected int or bool, got unit"
       | t -> failwith_lex_opt p (Printf.sprintf "'%s' is not of ground-type, but %s" s (Type.string_of_t t))
     end
  | GArith (op,gs,p) ->
     let newgs,newids =
       List.fold_right
         (fun g (gs,ids) -> let newg,newids = gprop_to_prop g ids st in (newg::gs , newids)) gs ([],[])
     in
     let prop = 
       match op with
       | Negate ->
          begin
            match newgs with
            | x :: [] ->  ~-. x
            | _ -> failwith_lex_opt p "unexpected number of arguments for negation"
          end
       | Add ->
          begin
            match newgs with
            | x :: y :: [] ->  x +. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for addition"
          end
       | Subtract ->
          begin
            match newgs with
            | x :: y :: [] ->  x -. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for subtraction"
          end
       | Multiply ->
          begin
            match newgs with
            | x :: y :: [] ->  x *. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for multiplication"
          end
       | Divide ->
          begin
            match newgs with
            | x :: y :: [] ->  x /. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for division"
          end
       | Modulo->
          begin
            match newgs with
            | x :: y :: [] ->  x %. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for modulus"
          end
       | And ->
          begin
            match newgs with
            | x :: y :: [] ->  x &&. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for conjunction"
          end
       | Or ->
          begin
            match newgs with
            | x :: y :: [] ->  x ||. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for disjunction"
          end
       | Not ->
          begin
            match newgs with
            | x :: [] ->  ~~. x
            | _ -> failwith_lex_opt p "unexpected number of arguments for negation"
          end
       | Equal ->
          begin
            match newgs with
            | x :: y :: [] ->  x ==. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for equality"
          end
       | Different ->
          begin
            match newgs with
            | x :: y :: [] ->  x <>. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for non-equality"
          end
       | Less ->
          begin
            match newgs with
            | x :: y :: [] ->  x <. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for less-than"
          end
       | Greater->
          begin
            match newgs with
            | x :: y :: [] ->  x <. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for greater-than"
          end
       | LessEQ->
          begin
            match newgs with
            | x :: y :: [] ->  x <=. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for less-or-equal-than"
          end
       | GreaterEQ->
          begin
            match newgs with
            | x :: y :: [] ->  x >=. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for greater-or-equal-than"
          end
       | Implies->
          begin
            match newgs with
            | x :: y :: [] ->  x =>. y
            | _ -> failwith_lex_opt p "unexpected number of arguments for implies"
          end
       | _ -> failwith_lex_opt p "Z3 pair operations not supported"
     in
     prop , newids


(* countersigma = not sat (sigma && notP && x=w) * sat (sigma && P && x=w) *)
let generalise_conditions gen sigma countersigma store abs flag print =
  if not(flag) then sigma , countersigma , None , [] , None, None
  else
    begin
      let fresh_AbsCon typ = let id = get_fresh_id () in AbsCon(id, typ, default_sname) , id in     
      match gen with
      | None -> sigma , countersigma , None , [] , None , None
      | Some (ws, ls, gprop) -> (* TODO: abs is of ref type, we need to get the type of the location*)
         let abs =
           match abs with
           | None -> List.map (fun (w,t) -> fst (fresh_AbsCon t)) ws
           | Some a ->
              if List.length a = List.length ws then a
              else failwith_lex_opt None "number of generalisation parameters does not match"
         in
         let multi_sub e = multi_beta_subst e (List.map fst ws) abs in
         let newls = List.map (fun (l,e) -> l, multi_sub e) ls in
         let newgprop = multi_beta_subst_gprop gprop (List.map fst ws) abs in
         let new_prop , new_ids = gprop_to_prop newgprop [] store in
         let newsigma , notsigma =
           let sigma0,dtree0 = sigma in
           let i3,id3 = fresh_AbsCon Type.BoolT in
           let dtree1 = Upto_tools.dt_add_id_notopt dtree0 id3 new_ids in
           let sigma1 = sigma_add_var id3 default_sname (sigma_add_beq id3 new_prop sigma0) in
           let notsigma1 = sigma_add_not_var id3 default_sname
                             (sigma_add_beq id3 new_prop (fst countersigma)) , (* not(P) *)
                           sigma_add_var id3 default_sname
                             (sigma_add_beq id3 new_prop (snd countersigma))   (* P *)
           in
           (sigma1,dtree1),notsigma1
         in
         let intersect_sigma =
           List.fold_right
             (fun (l,e) (acc1,acc2) ->
               let v = store_deref store (fst l) in
               match v with
               | None -> failwith_lex_opt (snd l) (Printf.sprintf "location %s not found" ((fst l).str))
               | Some v -> get_l_eq_prop (v,snd l) e acc1 ,
                           get_l_eq_prop (v,snd l) e acc2) 
             newls notsigma
         in
         print (Printf.sprintf "Counterexample sigma (generalisation invariant): \n%s\n"
                  (string_of_sigma (fst intersect_sigma)));
         print (Printf.sprintf "Counterexample sigma (generalisation value): \n%s\n"
                  (string_of_sigma (snd intersect_sigma)));
         print (Printf.sprintf "New sigma: \n%s\n" (string_of_sigma (fst newsigma)));
         newsigma , intersect_sigma , Some abs , newls , pos_of_g_prop gprop , gen
    end


let generalise gen store newls countersigma pos flag set_gen_success =
  if not(flag) then store
  else
    match gen with
    | None -> store
    | Some _ ->
       begin
         if check_sat_sigma (fst countersigma)
         then
           begin
             (Printf.printf "Following formula must not hold: \n%s\n\n"
                (string_of_sigma (fst countersigma)));
             (Printf.printf "Counterexample found: \n%s\n" (get_model_s ()));
             failwith_lex_opt pos "Generalisation proof failed: invariant does not hold"
           end
         else
           if check_sat_sigma (snd countersigma) then
             begin
               set_gen_success ();
               let newstore =
                 List.fold_right
                   (fun (l,e) acc -> store_update acc (fst l) (fo_val_of_exp e))
                   newls store
               in
               newstore
             end
           else
             begin
               (Printf.printf "An assignment must exist for the following formula: \n%s\n\n"
                  (string_of_sigma (snd countersigma)));
               (Printf.printf "Formula not satisfiable: location is not represented by generalisation.");
               failwith_lex_opt pos "Generalisation proof failed: value does not generalise store"
             end
       end
