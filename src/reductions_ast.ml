open Ast
open Z3api

(* type of store *)
module StoreMap = Map.Make(Location)
type store = value StoreMap.t
let list_of_store = StoreMap.bindings
let fold_store = StoreMap.fold

let string_of_s s =
  string_of_sequence ","
    (fun (k,v) ->
      Printf.sprintf "(%s |-> %s)"
        (string_of_loc k) (string_of_val v)) (StoreMap.bindings s)

let is_ho_value = function
  | ConstVal _ -> false
  | FunVal   _ -> true
  | AbsCon   _ -> false
  | AbsFun   _ -> true
  | TupleVal _ -> false (* check if this is the case *)
  | ListVal   _ -> false (* check if this is the case *) (* TODO *)

(* evaluation frames - ala CEK machines *)
type eval_frame =
  | ArithECxt   of arith_op * value list * expression list * (Lexing.position * Lexing.position) option
  | AppOpECxt   of expression * (Lexing.position * Lexing.position) option
  | AppRandECxt of value * (Lexing.position * Lexing.position) option
  | NewRefECxt  of loc * Type.t * expression * (Lexing.position * Lexing.position) option (* initialiser expression requires an eval cxt *)
  | AssignECxt  of loc * (Lexing.position * Lexing.position) option  
  | CondECxt    of expression * expression * (Lexing.position * Lexing.position) option 
  | LetECxt     of ident * Type.t * expression * (Lexing.position * Lexing.position) option 
  | LetTupleECxt of (ident * Type.t) list * expression * (Lexing.position * Lexing.position) option 
  | SeqECxt     of expression * (Lexing.position * Lexing.position) option          (* semicolon *)
  | TupleECxt   of value list * expression list * (Lexing.position * Lexing.position) option
  | TupleProjECxt of int * int * (Lexing.position * Lexing.position) option
  | TupleFstUpdECxt of int * int * expression * (Lexing.position * Lexing.position) option
  | TupleSndUpdECxt of value * int * int * (Lexing.position * Lexing.position) option
  | MatchECxt of Type.t * expression * ident * ident * expression *
                   (Lexing.position * Lexing.position) option

let rec string_of_eval_frame frame =
  match frame with
  | ArithECxt   (op,vs,es,p) ->
     Printf.sprintf "ArithCxt (%s;[%s];[%s];%s)"
       (string_of_op op)
       (string_of_sequence "," string_of_val vs)
       (string_of_sequence "," string_of_exp es)
       (string_of_pos_option p)
  | AppOpECxt   (e,p) ->
     Printf.sprintf "AppOpCxt (%s;%s)"
       (string_of_exp e)
       (string_of_pos_option p)
  | AppRandECxt (v,p) ->
     Printf.sprintf "AppRandCxt (%s;%s)"
       (string_of_val v)
       (string_of_pos_option p)
  | NewRefECxt  (l,t,e,p) ->
     Printf.sprintf "NewRefCxt (%s;%s;%s;%s)"
       (string_of_loc l)
       (Type.string_of_t t)
       (string_of_exp e)
       (string_of_pos_option p)
  | AssignECxt  (l,p) ->
     Printf.sprintf "AssignCxt (%s;%s)"
       (string_of_loc l)
       (string_of_pos_option p)
  | CondECxt    (e1,e2,p) ->
     Printf.sprintf "CondCxt (%s;%s;%s)"
       (string_of_exp e1)
       (string_of_exp e2)
       (string_of_pos_option p)
  | LetECxt     (id,t,e,p) ->
     Printf.sprintf "LetCxt (%s;%s;%s;%s)"
       (string_of_id id)
       (Type.string_of_t t)
       (string_of_exp e)
       (string_of_pos_option p)
  | LetTupleECxt (idts,e,p) ->
     Printf.sprintf "LetTupleCxt ([%s];%s;%s)"
       (string_of_sequence ","
          (fun (id,t) ->
            Printf.sprintf "(%s : %s)"
              (string_of_id id)
              (Type.string_of_t t)) idts)
       (string_of_exp e)
       (string_of_pos_option p)
  | SeqECxt     (e,p) ->
     Printf.sprintf "SeqCxt (%s;%s)"
       (string_of_exp e)
       (string_of_pos_option p)
  | TupleECxt   (vs,es,p) ->
     Printf.sprintf "SeqCxt ([%s];%s;%s)"
       (string_of_sequence "," string_of_val vs)
       (string_of_sequence "," string_of_exp es)
       (string_of_pos_option p)
  | TupleProjECxt (i,j,p) ->
     Printf.sprintf "TupleProjECxt ([%s/%s];%s)"
       (string_of_int i)
       (string_of_int j)
       (string_of_pos_option p)
  | TupleFstUpdECxt (i,j,e,p) -> 
     Printf.sprintf "TupleFstUpdECxt ([%s/%s:=%s];%s)"
       (string_of_int i)
       (string_of_int j)
       (string_of_exp e)
       (string_of_pos_option p)
  | TupleSndUpdECxt (v,i,j,p) ->
     Printf.sprintf "TupleSndUpdECxt (%s;[%s/%s:=];%s)"
       (string_of_val v)
       (string_of_int i)
       (string_of_int j)
       (string_of_pos_option p)
  | MatchECxt (t,e2,i1,i2,e3,p) ->
     Printf.sprintf "MatchECxt (%s,%s,%s,%s,%s;%s)"
       (Type.string_of_t t)
       (string_of_exp e2)
       (string_of_id i1)
       (string_of_id i2)
       (string_of_exp e3)
       (string_of_pos_option p)

(* the type of an evaluation context
 *
 * the head of the list is supposed to be the inner-most evaluation frame
 * *)
type eval_cxt = eval_frame list

let string_of_ecxt ecxt = string_of_sequence "::" string_of_eval_frame ecxt

(* A CEK expression is decomposed in two parts:
  * - an evaluation context
  * - an inner expression
  *
  * Taken by CEK machines
  * *)
type cek_exp = {ecxt: eval_cxt; e: expression}

let string_of_cek_exp {ecxt;e} =
  Printf.sprintf "{%s ; %s}"
    (string_of_ecxt ecxt)
    (string_of_exp e)

(* the reduction configuration *)
type red_conf = {s:store; e: cek_exp}

let string_of_red_conf {s;e} =
  Printf.sprintf "{s=%s;e=%s}" (string_of_s s) (string_of_cek_exp e)

(* store update
 * - Accepts store, location and value
 * - returns updated store
 * *)
let store_update s l v = StoreMap.add l v s
let store_deref s l = StoreMap.find_opt l s

module RedConf = struct
  type t = red_conf
  let compare a b = compare a b
end
module RedConfSet = Set.Make(RedConf)
