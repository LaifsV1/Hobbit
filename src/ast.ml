
type arith_op =
  | Negate 
  | Add 
  | Subtract 
  | Multiply 
  | Divide 
  | Modulo
  | And 
  | Or 
  | Not 
  | Equal 
  | Different 
  | Less 
  | Greater
  | LessEQ
  | GreaterEQ
  | Implies
  | Fst
  | Snd
  

(* used to give objects unique ids *)
type uniqueId = int

let int_of_uniqueId : uniqueId -> int =
  fun x -> x

let next_fresh_id = ref 0
let get_fresh_id () = let x = !next_fresh_id in next_fresh_id := !next_fresh_id + 1; x
let reset_fresh_id () = next_fresh_id := 0; ()
let default_acname = "ac"
let default_afname = "af"

(* identifiers *)
type ident = {idid:uniqueId; str:string}

(* store locations *)
type loc = {locid:uniqueId; str:string}
let mk_loc id str = {locid = id; str = str}
let loc_update_str loc s = {loc with str = s}

module Location = struct
  type t = loc
  let compare {locid=id1; str=str1}
              {locid=id2; str=str2} =
    match compare id1 id2 with
    | 0 -> 0
    | c -> c
end

type const = 
  | IntConst  of int
  | BoolConst of bool
  | UnitConst

type lex_pos_opt = (Lexing.position * Lexing.position) option

(*** GEN PROP STUFF ***)
type g_prop =
  | GConst of const * lex_pos_opt
  | GIdent of ident * lex_pos_opt
  | GArith of arith_op * g_prop list * lex_pos_opt
  | GAbsCon of uniqueId * Type.t * string * lex_pos_opt
  | GDeref  of loc * lex_pos_opt
let g_true_pos  pos = GConst(BoolConst true  , pos)
let g_false_pos pos = GConst(BoolConst false , pos)
let pos_of_g_prop g =
  match g with
  | GConst (_,p) -> p
  | GIdent (_,p) -> p
  | GArith (_, _, p) -> p
  | GAbsCon (_,_,_,p) -> p
  | GDeref (_,p) -> p
(*** END OF PROP STUFF ***)
type g_expr = ((ident * Type.t) list) * (((loc * lex_pos_opt) * expression) list) * g_prop
and

value =
  | ConstVal of const
  | TupleVal of value list
  (* Named function 
   * - 1st ident: name of function for recursive calls
   * - 1st Type.t: return type of function
   * - 2nd ident: formal argument identifier
   * - 2nd Type.t: type of argument
   * - expression: function body
   *
   * Note:
   * - unnamed, non-recursive functions have "_" as function name
   * - 0 argument functions have "_" as argument name and UnitT as argument type. They should be applied to '()' (unit value)
   * *)
  | FunVal of ident * Type.t * ident * Type.t * expression * (g_expr option)
  (* Abstract constants are named objects with a string prefix and a uniqueId to identify them.
   * They also carry their type which should be a base type (Bool/Int).
   * *)
  | AbsCon of uniqueId * Type.t * string
  (* Abstract functions are named objects with a string prefix and a uniqueId to identify them.
   * They also carry their type which is of the form t1 -> t2,
   * where t1 is the first, and t2 is the second Type.t.
   * *)
  | AbsFun of uniqueId * Type.t * Type.t * string
and

expression =
  | ValExp    of value * lex_pos_opt
  | IdentExp  of ident * lex_pos_opt
  | ArithExp  of arith_op * expression list * lex_pos_opt
  | AppExp    of expression * expression * lex_pos_opt
  | CondExp   of expression * expression * expression * lex_pos_opt
  | NewRefExp of loc * Type.t * expression * expression * lex_pos_opt
  | DerefExp  of loc * lex_pos_opt
  | AssignExp of loc * expression * lex_pos_opt
  | LetExp    of ident * Type.t * expression * expression * lex_pos_opt
  | LetTuple  of (ident * Type.t) list * expression * expression * lex_pos_opt
  | SeqExp    of expression * expression * lex_pos_opt   (* semicolon *)
  | TupleExp  of expression list * lex_pos_opt
  | BotExp    of lex_pos_opt
  | TupleProjExp   of expression * int * int * lex_pos_opt
  | TupleUpdExp of expression * int * int * expression * lex_pos_opt

type relation =
  | Equiv
  | Approx
  | ApproxInv

(* the program is two expressions and their relation *)

type program = {e1:expression; e2:expression; rel:relation * Type.t}

(* convenience functions *)

let string_of_position : Lexing.position -> string =
  fun {pos_fname ; pos_lnum ; pos_bol ; pos_cnum } ->
  Printf.sprintf "<line: %d, column: %d>" pos_lnum pos_cnum

let string_of_pos_option pos =
  match pos with
  | None -> "empty position"
  | Some (pos1,pos2) -> Printf.sprintf "%s,%s" (string_of_position pos1) (string_of_position pos2)

let get_lex_pos x = 
  match x with
  | ValExp (_, p) -> p
  | IdentExp (_, p) -> p
  | ArithExp (_, _, p) -> p
  | AppExp (_, _, p) -> p
  | CondExp (_, _, _, p) -> p
  | NewRefExp (_, _, _, _, p) -> p
  | DerefExp (_, p) -> p
  | AssignExp (_, _, p) -> p
  | LetExp (_, _, _, _, p) -> p
  | LetTuple (_, _, _, p) -> p
  | SeqExp (_, _, p) -> p
  | TupleExp (_, p) -> p
  | BotExp p -> p
  | TupleProjExp (_, _, _, p) -> p
  | TupleUpdExp  (_, _, _, _, p) -> p
(*
 * print the AST
 *
 * *)

let string_of_op op =
  match op with
  | Negate    -> "-"
  | Add       -> "+"
  | Subtract  -> "-"
  | Multiply  -> "*"
  | Divide    -> "/"
  | Modulo    -> "%"
  | And       -> "&&"
  | Or        -> "||"
  | Not       -> "not"
  | Equal     -> "=="
  | Different -> "<>"
  | Less      -> "<"
  | Greater   -> ">"
  | LessEQ    -> "<="
  | GreaterEQ -> ">="
  | Implies -> "=>"
  | Fst       -> "fst"
  | Snd       -> "snd"

let string_of_id {idid; str} =
  if str = "_" then "_"
  else str ^ "_" ^ (string_of_int idid)

let string_of_loc {locid = i; str = s} = s ^ "_" ^ (string_of_int i)

let string_of_const c =
  match c with
  | IntConst  i -> string_of_int i
  | BoolConst b -> string_of_bool b
  | UnitConst   -> "()"

let rec string_of_gprop = function
  | GConst (c,_) -> string_of_const c
  | GIdent (i,_) -> string_of_id i
  | GArith (op,gs,_) -> Printf.sprintf "(%s %s)"
                          (string_of_op op)
                          (String.concat " " (List.map string_of_gprop gs))
  | GAbsCon (i,t,s,_) -> Printf.sprintf "(%s%d:%s)"
                           s i (Type.string_of_t t)
  | GDeref  (l, p) -> "!" ^ (string_of_loc l)

let rec string_of_gen = function
  | (its, lpes, gprop) -> (*((ident * Type.t) list) * (((loc * lex_pos_opt) * expression) list) * g_prop*)
     let its_string = String.concat ","
                        (List.map (fun (i,t) ->
                             Printf.sprintf "(%s : %s)" (string_of_id i) (Type.string_of_t t)) its)
     in
     let lpes_string = String.concat ","
                        (List.map (fun ((l,_),e) ->
                             Printf.sprintf "(%s as %s)" (string_of_loc l) (string_of_exp e)) lpes)
     in
     let gprop_string = string_of_gprop gprop in
     Printf.sprintf "{ %s | %s | %s }" its_string lpes_string gprop_string
     
and string_of_val v =
  let rec iter f = function
    | [] -> ""
    | [i] -> f i
    | i :: rest -> (f i) ^ ", " ^ (iter f rest)
  in
   match v with
  | ConstVal c  -> string_of_const c
  | TupleVal (vs) -> "(" ^ (iter string_of_val vs) ^ ")"
  | FunVal (fid, ft, param, pt, e, gen) ->
     let gen_string = match gen with None -> "" | Some gen -> (string_of_gen gen) in
     Printf.sprintf "(fix %s. fun %s :(%s -> %s) %s -> %s)"
       (string_of_id fid)
       (string_of_id param)
       (Type.string_of_t pt)
       (Type.string_of_t ft)
       gen_string
       (string_of_exp e)
  | AbsCon (i, t, s) -> "(" ^ s ^ (string_of_int i) ^ ": " ^ (Type.string_of_t t) ^ ")"
  | AbsFun  (i, t1, t2, s) -> "(" ^ s ^ (string_of_int i) ^ ": " ^ (Type.string_of_t t1) ^ "->" ^ (Type.string_of_t t2) ^ ")"

and string_of_exp exp =
  let rec iter f = function
    | [] -> ""
    | [i] -> f i
    | i :: rest -> (f i) ^ ", " ^ (iter f rest)
  in
  match exp with
  | ValExp    (v, p) -> string_of_val v
  | IdentExp  (id, p) -> string_of_id id
  | ArithExp  (op, es, p) ->
      let esStr = List.fold_left (fun out -> fun e -> if out = "" then string_of_exp e else out ^ " " ^ (string_of_exp e)) "" es in
      "{" ^ (string_of_op op) ^ " " ^ esStr ^ "}"
  | AppExp    (e1, e2, p) ->
      "{" ^ (string_of_exp e1) ^ " " ^ (string_of_exp e2) ^ "}"
  | CondExp   (e1, e2, e3, p) -> "if (" ^ (string_of_exp e1) ^ ")then {" ^ (string_of_exp e2) ^ "}else {" ^ (string_of_exp e3) ^ "}"
  | NewRefExp (l, lt, e1, e2, p) ->
    "ref " ^ (string_of_loc l) ^ ": " ^ (Type.string_of_t lt) ^ " = {" ^ (string_of_exp e1) ^ "} in{" ^ (string_of_exp e2) ^ "}"
  | DerefExp  (l, p) -> "!" ^ (string_of_loc l)
  | AssignExp (l, e, p) -> (string_of_loc l) ^ " := " ^ (string_of_exp e)
  | LetExp    (i, it, e1, e2, p) -> "let " ^ (string_of_id i) ^ ": " ^ (Type.string_of_t it) ^ " = {" ^ (string_of_exp e1) ^ "} in {" ^ (string_of_exp e2) ^ "}"
  | LetTuple  (is_ts, e1, e2, p) -> "let (" ^ (iter (fun (id, _) -> string_of_id id) is_ts) ^ "):(" ^ (iter (fun (_, it) -> Type.string_of_t it) is_ts) ^ ") = {" ^ (string_of_exp e1) ^ "} in {" ^ (string_of_exp e2) ^ "}"
  | SeqExp    (e1, e2, p) -> "{" ^ (string_of_exp e1) ^ ";" ^ (string_of_exp e2) ^ "}"
  | TupleExp  (es, p) -> "(" ^ (iter string_of_exp es) ^ ")"
  | BotExp    p -> "_bot_"
  | TupleProjExp (e1, i, j, p) -> (string_of_exp e1) ^ "[" ^ (string_of_int i) ^ "/" ^ (string_of_int j) ^ "]"
  | TupleUpdExp  (e1, i, j, e2, p) ->  (string_of_exp e1) ^ "[" ^ (string_of_int i) ^ "/" ^ (string_of_int j) ^ ":=" ^ (string_of_exp e2) ^ "]"

let string_of_pgm {e1 = e1; e2 = e2; rel = (r, t)} =
  (string_of_exp e1) ^ "\n" ^ (
    match r with
    | Equiv     -> "|||"
    | Approx    -> "|<|"
    | ApproxInv -> "|>|"
  ) ^ "_" ^ (Type.string_of_t t) ^ "\n" ^
  (string_of_exp e2)
