(* This file contains an API to interface with Z3's API *)
(* It currently uses its own AST since it is easier to manipulate, but I may change it *)
(* API functions are defined at the bottom of this file. *)

(*************************************************************
 * SOLVER FUNCTIONS:                                         *
 * -----------------                                         *
 * check_sat      : prop -> bool                             *
 * get_model_s    : unit -> string                           *
 * string_of_prop : prop -> string                           *
 *                                                           *
 * CONSTANTS:                                                *
 * ----------                                                *
 * _true  : prop            (true constant)                  *
 * _false : prop            (false constant)                 *
 * _int   : int -> prop     (integer constant)               *
 * _sint  : string -> prop  (symbolic integer)               *
 * _sbool : string -> prop  (symbolic boolean)               *
 *                                                           *
 * OPERATORS (REDUCE WHERE CONCRETISABLE):                   *
 * ---------------------------------------                   *
 * ( ~~. ) : prop -> prop          (prefix NOT)              *
 * ( ~-. ) : prop -> prop          (prefix UNARY MINUS)      *
 *                                                           *
 * ( ==. ) : prop -> prop -> prop (infix EQUALS)             *
 * ( <>. ) : prop -> prop -> prop (infix DIFFERENT)          *
 * ( =>. ) : prop -> prop -> prop (infix IMPLIES)            *
 * ( ||. ) : prop -> prop -> prop (infix OR)                 *
 * ( &&. ) : prop -> prop -> prop (infix AND)                *
 *                                                           *
 * ( <.  ) : prop -> prop -> prop (infix LESS THAN)          *
 * ( <=. ) : prop -> prop -> prop (infix LESS THAN EQUAL)    *
 * ( >.  ) : prop -> prop -> prop (infix GREATER THAN)       *
 * ( >=. ) : prop -> prop -> prop (infix GREATER THAN EQUAL) *
 *                                                           *
 * ( +. ) : prop -> prop -> prop (infix ADDITION)            *
 * ( *. ) : prop -> prop -> prop (infix MULTIPLICATION)      *
 * ( -. ) : prop -> prop -> prop (infix SUBTRACTION)         *
 *                                                           *
 * ( /. ) : prop -> prop -> prop (infix DIVISION)            *
 *************************************************************)

open Z3
open Z3.Symbol
open Z3.Sort
open Z3.Expr
open Z3.Boolean
open Z3.FuncDecl
open Z3.Goal
open Z3.Tactic
open Z3.Tactic.ApplyResult
open Z3.Probe
open Z3.Solver
open Z3.Arithmetic
open Z3.Arithmetic.Integer
open Z3.Arithmetic.Real
open Z3.BitVector
open Format

let ctx = Z3.mk_context []
let solver = Z3.Solver.mk_simple_solver ctx


(* sorts *)
let int_sort_z3  = Integer.mk_sort ctx
let bool_sort_z3 = Boolean.mk_sort ctx


(* constructors *)
let str_symbol_z3 x = Symbol.mk_string ctx x

let var_int_z3  x = Integer.mk_const ctx (str_symbol_z3 x)
let var_bool_z3 x = Boolean.mk_const ctx (str_symbol_z3 x)

let int_i_z3 i = Integer.mk_numeral_i ctx i
let int_s_z3 s = Integer.mk_numeral_s ctx s

let true_z3  = Boolean.mk_true  ctx
let false_z3 = Boolean.mk_false ctx


(* bool ops *)
let not_z3 e         = Boolean.mk_not ctx e
let or_z3 es         = Boolean.mk_or  ctx es
let and_z3 es        = Boolean.mk_and ctx es
let eq_z3 e1 e2      = Boolean.mk_eq  ctx e1 e2
let ite_z3 eb e1 e2  = Boolean.mk_ite ctx eb e1 e2
let implies_z3 e1 e2 = Boolean.mk_implies ctx e1 e2


(* int ops *)
let lt_z3 e1 e2  = Arithmetic.mk_lt ctx e1 e2
let le_z3 e1 e2  = Arithmetic.mk_le ctx e1 e2
let gt_z3 e1 e2  = Arithmetic.mk_gt ctx e1 e2
let ge_z3 e1 e2  = Arithmetic.mk_ge ctx e1 e2
let add_z3 es    = Arithmetic.mk_add ctx es
let mul_z3 es    = Arithmetic.mk_mul ctx es
let sub_z3 es    = Arithmetic.mk_sub ctx es
let div_z3 e1 e2 = Arithmetic.mk_div ctx e1 e2
let uminus_z3 e1 = Arithmetic.mk_unary_minus ctx e1
let mod_z3 e1 e2 = Arithmetic.Integer.mk_mod ctx e1 e2

(* unparsing *)
let string_of_z3 e = Expr.to_string e

(* solver operations *)
let check es =
  match Z3.Solver.check solver es with  
  | UNSATISFIABLE -> false
  | UNKNOWN       -> failwith (sprintf "couldn't check if sat: %s"
                                 (string_of_z3 (and_z3 es)))
  | SATISFIABLE   -> true

let get_model () =
  match Z3.Solver.get_model solver with
  | None -> failwith "couldn't get model"
  | Some m -> m


(* data type for propositions *)
type prop = IntProp of int
          | BoolProp of bool
          | VarIntProp of string
          | VarBoolProp of string
          | AndProp of (prop list)
          | OrProp  of (prop list)
          | NotProp of prop
          | EqProp  of (prop * prop)
          | IteProp of (prop * prop * prop)
          | ImpliesProp  of (prop * prop)
          | LtProp of (prop * prop)
          | LeProp of (prop * prop)
          | GtProp of (prop * prop)
          | GeProp of (prop * prop)
          | AddProp of (prop list)
          | MulProp of (prop list)
          | SubProp of (prop list)
          | DivProp of (prop * prop)
          | ModProp of (prop * prop)
          | UminusProp of prop

let rec z3_of_prop prop =
  match prop with
  | IntProp i      -> int_i_z3 i
  | BoolProp true  -> true_z3
  | BoolProp false -> false_z3
  | VarIntProp  s  -> var_int_z3 s
  | VarBoolProp s  -> var_bool_z3 s
  | AndProp props  -> and_z3 (List.map z3_of_prop props)
  | OrProp  props  -> or_z3  (List.map z3_of_prop props)
  | NotProp prop   -> not_z3 (z3_of_prop prop)
  | EqProp (p1,p2) -> eq_z3 (z3_of_prop p1) (z3_of_prop p2)
  | IteProp (pb,p1,p2) -> ite_z3
                            (z3_of_prop pb)
                            (z3_of_prop p1)
                            (z3_of_prop p2)
  | ImpliesProp (p1,p2) -> implies_z3 (z3_of_prop p1) (z3_of_prop p2)
  | LtProp (p1,p2) -> lt_z3 (z3_of_prop p1) (z3_of_prop p2)
  | LeProp (p1,p2) -> le_z3 (z3_of_prop p1) (z3_of_prop p2)
  | GtProp (p1,p2) -> gt_z3 (z3_of_prop p1) (z3_of_prop p2)
  | GeProp (p1,p2) -> ge_z3 (z3_of_prop p1) (z3_of_prop p2)
  | AddProp props -> add_z3 (List.map z3_of_prop props)
  | MulProp props -> mul_z3 (List.map z3_of_prop props)
  | SubProp props -> sub_z3 (List.map z3_of_prop props)
  | DivProp (p1,p2) -> div_z3 (z3_of_prop p1) (z3_of_prop p2)
  | ModProp (p1,p2) -> mod_z3 (z3_of_prop p1) (z3_of_prop p2)
  | UminusProp p1 -> uminus_z3 (z3_of_prop p1)

(* API functions *)
(* check_sat : prop -> bool, get_model_s : unit -> string *)
let check_sat prop = check [z3_of_prop prop]
let get_model_s () = Z3.Model.to_string (get_model ())
let rec string_of_prop prop =
  match prop with
  | IntProp i      -> string_of_int i
  | BoolProp true  -> "true"
  | BoolProp false -> "false"
  | VarIntProp  s  -> s
  | VarBoolProp s  -> s
  | AndProp props  -> Printf.sprintf "(%s)" (String.concat " and " (List.map string_of_prop props))
  | OrProp  props  -> Printf.sprintf "(%s)" (String.concat " or " (List.map string_of_prop props))
  | NotProp prop   -> Printf.sprintf "(not %s)" (string_of_prop prop)
  | EqProp (p1,p2) -> Printf.sprintf "(%s = %s)"
                        (string_of_prop p1) (string_of_prop p2)
  | IteProp (pb,p1,p2) -> Printf.sprintf "(%s ? %s : %s)"
                            (string_of_prop pb) (string_of_prop p1) (string_of_prop p2)
  | ImpliesProp (p1,p2) -> Printf.sprintf "(%s => %s)"
                             (string_of_prop p1) (string_of_prop p2)
  | LtProp (p1,p2) -> Printf.sprintf "(%s < %s)"
                        (string_of_prop p1) (string_of_prop p2)
  | LeProp (p1,p2) -> Printf.sprintf "(%s <= %s)"
                        (string_of_prop p1) (string_of_prop p2)
  | GtProp (p1,p2) -> Printf.sprintf "(%s > %s)"
                        (string_of_prop p1) (string_of_prop p2)
  | GeProp (p1,p2) -> Printf.sprintf "(%s >= %s)"
                        (string_of_prop p1) (string_of_prop p2)
  | AddProp props -> Printf.sprintf "(%s)" (String.concat " + " (List.map string_of_prop props))
  | MulProp props -> Printf.sprintf "(%s)" (String.concat " * " (List.map string_of_prop props))
  | SubProp props -> Printf.sprintf "(%s)" (String.concat " - " (List.map string_of_prop props))
  | DivProp (p1,p2) -> Printf.sprintf "(/ %s %s)"
                         (string_of_prop p1) (string_of_prop p2)
  | ModProp (p1,p2) -> Printf.sprintf "(mod %s %s)"
                         (string_of_prop p1) (string_of_prop p2)
  | UminusProp p1 -> Printf.sprintf "(-%s)" (string_of_prop p1)

(* prop builders *)
let _true  = BoolProp true    (* true *)
let _false = BoolProp false   (* false *)
let _int i = IntProp i        (* int *)
let _sint  x = VarIntProp  x  (* symbolic int *)
let _sbool x = VarBoolProp x  (* symbolic bool *)

(* prefix NOT operator *)
let ( ~~. ) p =
  match p with
  | BoolProp false -> BoolProp true
  | BoolProp true  -> BoolProp false
  | _ -> NotProp p

(* prefix unary minus *)
let ( ~-. ) p =
  match p with
  | IntProp i -> IntProp (-i)
  | _ -> UminusProp p

(* infix EQUALS *)
let ( ==. ) p1 p2 =
  (*Printf.printf "==. %s %s \n" (string_of_prop p1) (string_of_prop p2);*)
  match p1,p2 with
  | BoolProp true , BoolProp false | BoolProp false , BoolProp true -> BoolProp false
  | IntProp i, IntProp j -> if j = i then BoolProp true else BoolProp false
  | _ -> EqProp (p1,p2)

(* infix DIFFERENT *)
let ( <>. ) p1 p2 =
  match p1,p2 with
  | BoolProp true , BoolProp false | BoolProp false , BoolProp true -> BoolProp true
  | IntProp i, IntProp j -> if j <> i then BoolProp true else BoolProp false
  | _ -> NotProp (EqProp (p1,p2))

(* infix IMPLIES *)
let ( =>. ) p1 p2 =
  match p1 with
  | BoolProp true  -> p2
  | BoolProp false -> BoolProp true (* vacuous truth *)
  | _      -> ImpliesProp (p1,p2)

(* infix OR *)
let ( ||. ) p1 p2 =
  match p1,p2 with
  | BoolProp true , _ | _ , BoolProp true -> BoolProp true
  | BoolProp false , BoolProp false -> BoolProp false
  | BoolProp false , _ -> p2
  | _ , BoolProp false -> p1
  | OrProp p1 , OrProp p2 -> OrProp (p1 @ p2)
  | OrProp p1 , p2        -> OrProp (p1 @ [p2])
  |        p1 , OrProp p2 -> OrProp (p1 :: p2)
  | _ -> OrProp [p1;p2]

(* infix AND *)
let ( &&. ) p1 p2 =
  match p1,p2 with
  | BoolProp false , _ | _ , BoolProp false -> BoolProp false
  | BoolProp true , BoolProp true -> BoolProp true
  | BoolProp true , _ -> p2
  | _ , BoolProp true -> p1
  | AndProp p1 , AndProp p2 -> AndProp (p1 @ p2)
  | AndProp p1 , p2         -> AndProp (p1 @ [p2])
  |         p1 , AndProp p2 -> AndProp (p1 :: p2)
  | _ -> AndProp [p1;p2]

(* todo: compute where possible, e.g. int + int *)
(* infix less than *)
let ( <.  ) p1 p2 =
  match p1,p2 with
  | IntProp i, IntProp j -> if i < j then BoolProp true else BoolProp false
  | _ -> LtProp (p1,p2)

(* infix less than or equal *)
let ( <=. ) p1 p2 =
  match p1,p2 with
  | IntProp i, IntProp j -> if i <= j then BoolProp true else BoolProp false
  | _ -> LeProp (p1,p2)

(* infix greater than *)
let ( >.  ) p1 p2 =
  match p1,p2 with
  | IntProp i, IntProp j -> if i > j then BoolProp true else BoolProp false
  | _ -> GtProp (p1,p2)

(* infix greater than or equal *)
let ( >=. ) p1 p2 =
  match p1,p2 with
  | IntProp i, IntProp j -> if i >= j then BoolProp true else BoolProp false
  | _ -> GeProp (p1,p2)

(* infix addition *)
let ( +. ) p1 p2 =
  match p1,p2 with
  | IntProp i, IntProp j -> IntProp (i + j)
  | _ -> AddProp [p1;p2]

(* infix multiplication *)
let ( *. ) p1 p2 =
  match p1,p2 with
  | IntProp i, IntProp j -> IntProp (i * j)
  | _ -> MulProp [p1;p2]

(* infix subtraction *)
let ( -. ) p1 p2 =
  match p1,p2 with
  | IntProp i, IntProp j -> IntProp (i - j)
  | _ -> SubProp [p1;p2]

(* infix division *)
(* no reduction because Z3's div is different from OCaml's *)
let ( /. ) p1 p2 =
  match p1,p2 with
  | _, IntProp j -> if j=0 then failwith "z3 api: DIV by 0" else DivProp (p1,p2)
  | _ -> DivProp (p1,p2)

(* infix mod *)
(* no reduction because Z3's div is different from OCaml's *)
let ( %. ) p1 p2 =
  match p1,p2 with
  | _, IntProp j -> if j=0 then failwith "z3 api: MOD by 0" else ModProp(p1,p2)
  | _ -> ModProp(p1,p2)


type sigma_prop = TopIntVarConstNeq of ((int * string) * int)
                | TopBoolVarConstNeq of ((int * string) * bool)
                | TopIntVarNeq of ((int * string) * (int * string))
                | TopBoolVarNeq of ((int * string) * (int * string))
                | TopIntEq of (int * prop)
                | TopBoolEq of (int * prop)
                | TopBoolVar of (int * string)
                | TopNotBoolVar of (int * string)
type sigma = sigma_prop list

let sigma_add_iconst_neq : (int * string) -> int -> sigma -> sigma =
  fun v1 v2 sigma -> TopIntVarConstNeq(v1 , v2) :: sigma

let sigma_add_bconst_neq : (int * string) -> bool -> sigma -> sigma =
  fun v1 v2 sigma -> TopBoolVarConstNeq(v1 , v2) :: sigma

let sigma_add_ivar_neq : (int * string) -> (int * string) -> sigma -> sigma =
  fun v1 v2 sigma -> TopIntVarNeq(v1 , v2) :: sigma

let sigma_add_bvar_neq : (int * string) -> (int * string) -> sigma -> sigma =
  fun v1 v2 sigma -> TopBoolVarNeq(v1 , v2) :: sigma

let sigma_add_ieq : int -> prop -> sigma -> sigma =
  fun new_id new_expr sigma ->
  TopIntEq(new_id , new_expr) :: sigma

let sigma_add_beq : int -> prop -> sigma -> sigma =
  fun new_id new_expr sigma ->
  TopBoolEq(new_id , new_expr) :: sigma

let sigma_add_var : int -> string -> sigma -> sigma =
  fun new_id new_str sigma ->
  TopBoolVar(new_id, new_str) :: sigma

let sigma_add_not_var : int -> string -> sigma -> sigma =
  fun new_id new_str sigma ->
  TopNotBoolVar(new_id, new_str) :: sigma

let default_sname = "w"

let name_of_id id = Printf.sprintf "%s_%d" default_sname id
let name_of_iv iv = Printf.sprintf "%s_%d" (snd iv) (fst iv)

let sigma_add_iid_neq : int -> int -> sigma -> sigma =
  fun v1 v2 sigma -> TopIntVarNeq((v1,default_sname) , (v2,default_sname)) :: sigma

let sigma_add_bid_neq : int -> int -> sigma -> sigma =
  fun v1 v2 sigma -> TopBoolVarNeq((v1,default_sname) , (v2,default_sname)) :: sigma

let sbool_of_id id = _sbool (name_of_id id)
let sint_of_id  id = _sint  (name_of_id id)
let sbool_of_id_var iv = _sbool (name_of_iv iv)
let sint_of_id_var  iv = _sint  (name_of_iv iv)

let default_pair_of_id id = (id , default_sname)

let prop_of_sigma : sigma -> prop =
  fun sigma ->
  let rec aux sigma acc =
    match sigma with
    | [] -> acc
    | TopIntVarConstNeq (iv,i) :: xs ->
       aux xs (acc &&. (~~.((sint_of_id_var iv) ==. (_int i))))
    | TopBoolVarConstNeq (iv,true) :: xs ->
       aux xs (acc &&. (~~.((sint_of_id_var iv) ==. (_true))))
    | TopBoolVarConstNeq (iv,false) :: xs ->
       aux xs (acc &&. (~~.((sint_of_id_var iv) ==. (_false))))
    | TopIntVarNeq (iv1 , iv2) :: xs ->
       aux xs (acc &&. (~~.((sint_of_id_var iv1) ==. (sint_of_id_var iv2))))
    | TopBoolVarNeq (iv1 , iv2) :: xs ->
       aux xs (acc &&. (~~.((sbool_of_id_var iv1) ==. (sbool_of_id_var iv2))))
    | TopIntEq (id , prop) :: xs -> aux xs (acc &&. ((sint_of_id id) ==. prop))
    | TopBoolEq (id , prop) :: xs -> aux xs (acc &&. ((sbool_of_id id) ==. prop))
    | TopBoolVar (id , str) :: xs -> aux xs (acc &&. (sbool_of_id_var (id , str)))
    | TopNotBoolVar (id , str) :: xs -> aux xs (acc &&. (~~. (sbool_of_id_var (id , str))))
  in
  aux sigma _true
  
let is_sigma_empty : sigma -> bool = function
  | [] -> true
  | _ -> false

let string_of_sigmaprop prop =
  match prop with
  | TopIntVarConstNeq (iv,i) -> Printf.sprintf "(%s <> %d)" (name_of_iv iv) i
  | TopBoolVarConstNeq (iv,true) -> Printf.sprintf "(%s <> true)" (name_of_iv iv)
  | TopBoolVarConstNeq (iv,false) -> Printf.sprintf "(%s <> false)" (name_of_iv iv)
  | TopIntVarNeq (iv1 , iv2) -> Printf.sprintf "(%s <> %s)" (name_of_iv iv1) (name_of_iv iv2)
  | TopBoolVarNeq (iv1 , iv2) -> Printf.sprintf "(%s <> %s)" (name_of_iv iv1) (name_of_iv iv2)
  | TopIntEq (id , prop) -> Printf.sprintf "(%s = %s)" (name_of_id id) (string_of_prop prop)
  | TopBoolEq (id , prop) -> Printf.sprintf "(%s = %s)" (name_of_id id) (string_of_prop prop)
  | TopBoolVar (id , str) -> Printf.sprintf "%s" (name_of_iv (id,str)) 
  | TopNotBoolVar (id , str) -> Printf.sprintf "(not %s)" (name_of_iv (id,str))

let string_of_sigma sigma = String.concat " and \n" (List.map string_of_sigmaprop sigma)
let check_sat_sigma sigma =
  match sigma with
  | [] -> true
  | _ ->
     let z3_of_sigma_prop sigma =
       match sigma with
       | TopIntVarConstNeq (iv,i) ->
          not_z3 (
              eq_z3
                (var_int_z3 (name_of_iv iv))
                (int_i_z3 i))
       | TopBoolVarConstNeq (iv,true) ->
          not_z3 (
              eq_z3
                (var_bool_z3 (name_of_iv iv))
                true_z3)
       | TopBoolVarConstNeq (iv,false) ->
          not_z3 (
              eq_z3
                (var_bool_z3 (name_of_iv iv))
                false_z3)
       | TopIntVarNeq (iv1 , iv2) ->
          not_z3 (
              eq_z3
                (var_int_z3 (name_of_iv iv1))
                (var_int_z3 (name_of_iv iv2)))
       | TopBoolVarNeq (iv1 , iv2) ->
          not_z3 (
              eq_z3
                (var_bool_z3 (name_of_iv iv1))
                (var_bool_z3 (name_of_iv iv2)))
       | TopIntEq (id , prop) ->
          eq_z3
            (var_int_z3 (name_of_id id))
            (z3_of_prop prop)
       | TopBoolEq (id , prop) ->
          eq_z3
            (var_bool_z3 (name_of_id id))
            (z3_of_prop prop)
       | TopBoolVar (id , str) -> var_bool_z3 (name_of_iv (id,str))
       | TopNotBoolVar (id , str) -> not_z3 (var_bool_z3 (name_of_iv (id,str)))
     in
     check (List.map z3_of_sigma_prop sigma)


