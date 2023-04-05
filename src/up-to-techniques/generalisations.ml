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
  let fresh_AbsCon typ = let id = get_fresh_id () in AbsCon(id, typ, default_sname, None) , id in     
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

let rec gprop_to_sigma gprop (sigma,dtree) countersig st =
  match gprop with
  | GIdent (i,p) -> failwith_lex_opt p "gprop_to_sigma (1): expected ground-type value"
  | GConst (UnitConst,p) -> failwith_lex_opt p "gprop_to_sigma (2): expected int or bool, got unit"
  | GConst (v,p) -> ConstVal v , (sigma,dtree) , countersig
  | GDeref (l,p) ->
     begin
       match store_deref st l with
       | None -> failwith_lex_opt p "gprop_to_sigma (3): location unbound"
       | Some v -> v , (sigma,dtree) , countersig
     end
  | GAbsCon (i,t,s,p) -> AbsCon (i, t, s, None) , (sigma,dtree) , countersig
  | GArith (op,gs,p) ->
     let gs',(sigma',dtree'),(fst_csigma',snd_csigma') =
       List.fold_right (* fold_right to preserve order *)
         (fun gprop (acc_gs,acc_sigma,acc_countsig) ->
           let new_v, new_sigma , new_countersig = gprop_to_sigma gprop acc_sigma acc_countsig st in
           new_v :: acc_gs, new_sigma, new_countersig) gs ([],(sigma,dtree),countersig)
     in
     (** NOTE: assuming all the res produce the same thing when processed with reduce_arith **)
     (** NOTE: there appears to be some invariant with Sigma GC where it collects x = v.
         Wouldn't happen normally by calling the Reduction semantics because
         concrete operations are reduced where possible. **)
     (** TODO: test if you can remove sndcsig. **)
     match reduce_arith op gs' p ([], dtree') Z3api.default_sname with
     | Some(ValExp (v1,p1) , (sigma_updates , new_dtree)) ->
        v1 , (sigma_updates @ sigma',new_dtree) ,
        (sigma_updates @ fst_csigma', sigma_updates @ snd_csigma')
     | _ -> failwith_lex_opt p "gprop_to_sigma (4): unexpected None when reducing arith op"

(* countersigma = not sat (sigma && notP && x=w) * sat (sigma && P && x=w) *)
let generalise_conditions gen sigma countersigma store abs flag print =
  if not(flag) then sigma , countersigma , None , [] , None, None
  else
    begin
      let fresh_AbsCon typ m =
        let id = get_fresh_id () in AbsCon(id, typ, default_sname, m) , id
      in
      match gen with
      | None -> sigma , countersigma , None , [] , None , None
      | Some (ws, ls, gprop) ->
         (* TODO: abs is of ref type, we need to get the type of the location*)
         let abs =
           match abs with
           | None -> List.map (fun (w,t,m) -> fst (fresh_AbsCon t (Some m))) ws
           | Some a ->
              if List.length a = List.length ws then a
              else failwith_lex_opt None "number of generalisation parameters does not match"
         in
         let multi_sub e = multi_beta_subst e (List.map (fun (a,_,_) -> a) ws) abs in
         let newls = List.map (fun (l,e) -> l, multi_sub e) ls in
         let newgprop = multi_beta_subst_gprop gprop (List.map (fun (a,_,_) -> a) ws) abs in        
         let i3 , (sigma0,dtree0), csigma0 =  gprop_to_sigma newgprop sigma countersigma store in
         let newsigma , notsigma =
           (** NOTE: we aren't updating dtree0 because we aren't creating new IDs...? **)
           match i3 with
           | AbsCon (id3,t,_,_) ->
              begin
                match t with
                | Type.BoolT ->
                   let sigma1    = sigma_add_var     id3 default_sname sigma0 in
                   let notsigma1 = sigma_add_not_var id3 default_sname (fst csigma0) , (* not(P) *)
                                   sigma_add_var     id3 default_sname (snd csigma0)   (* P *)
                   in
                   (sigma1,dtree0),notsigma1
                | t -> failwith (Printf.sprintf "generalise_conditions: unexpected val %s, %s"
                                   (string_of_val i3) (string_of_gprop newgprop))
              end
           | ConstVal (BoolConst true) ->
              let sigma1    = sigma0 in
              let notsigma1 = sigma_set_false (fst csigma0) , (* not(P) *)
                              (snd csigma0)                   (* P *)
              in
              (sigma1,dtree0),notsigma1
           | ConstVal (BoolConst false) ->
              let sigma1    = sigma_set_false sigma0 in
              let notsigma1 = (fst csigma0) ,                 (* not(P) *)
                              sigma_set_false (snd csigma0)   (* P *)
              in
              (sigma1,dtree0),notsigma1
           | v ->
              failwith
                (Printf.sprintf "generalise_conditions: unexpected value %s" (string_of_val v))
         in
         let intersect_sigma =
           List.fold_right
             (fun (l,e) (acc1,acc2) ->
               let v = store_deref store (fst l) in
               match v with
               | None -> failwith_lex_opt (snd l)
                           (Printf.sprintf "intersect_sigma: location <%s> not found" ((fst l).str))
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
               (print_endline
                  "Formula not satisfiable: location is not represented by generalisation.");
               failwith_lex_opt pos "Generalisation proof failed: value does not generalise store"
             end
       end
