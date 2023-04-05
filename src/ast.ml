(* Monadic Operations to intimidate people *)
let return x = Some x
let (>>=) x f =
  match x with
  | Some v -> f v
  | None   -> None
let (>>) x y = x >>= (fun _ -> y)
let (let*) x f = x >>= f

(* Applicative Functor to intimidate the rest *)
let pure x = Some x
let (<*>) fo xo =
  match fo, xo with
  | Some f, Some x  -> Some (f x)
  | _               -> None

(* Function Composition *)
let (<|) f g x = f(g(x))
let (|>) f g x = g(f(x))

(* Actual Start of File *)
(* special name just for sync function *)
let sync_string = "_sync_" 

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
  | ListCons
  | PrintOp

(* used to give objects unique ids *)
type uniqueId = int

let int_of_uniqueId : uniqueId -> int =
  fun x -> x

let next_fresh_id = ref 0
let get_fresh_id () = let x = !next_fresh_id in next_fresh_id := !next_fresh_id + 1; x
let reset_fresh_id () = next_fresh_id := 0; ()
let default_acname = "ac"
let default_afname = "af"
let default_alname = "al"

type marker = int (* to prove variables produced by generalisation/invariants are equal *)
let next_fresh_marker = ref 0
let get_fresh_marker () = let x = !next_fresh_marker in next_fresh_marker := !next_fresh_marker + 1; x
let reset_fresh_marker () = next_fresh_marker := 0; ()

(* identifiers *)
type ident = {idid:uniqueId; str:string}
let string_of_id {idid; str} =
  if str = "_" then "_"
  else str ^ "_" ^ (string_of_int idid)

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
let string_of_loc {locid = i; str = s} = s ^ "_" ^ (string_of_int i)

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
type 'a sym_list = Nil | AbsList of ident | Cons of 'a * ('a sym_list)
module SymList = struct
  type 'a t = 'a sym_list
  let empty () = Nil
  let rec to_string f = function
    | Nil -> "[]"
    | AbsList id -> Printf.sprintf "(%s : symbolic_list)" (string_of_id id)
    | Cons (a,ls) -> Printf.sprintf "%s :: %s" (f a) (to_string f ls)
  let rec fold_left f1 f2 acc = function (* acc : None or Some (id,t) -> _ *)
    | Nil -> f2 acc None
    | AbsList id -> f2 acc (Some id)
    | Cons (x,xs) -> fold_left f1 f2 (f1 acc x) xs
  let rec fold_right f1 f2 ls acc = match ls with
    | Nil -> f2 acc None
    | AbsList id -> f2 acc (Some id)
    | Cons (x,xs) -> f1 x (fold_right f1 f2 xs acc)
  let rec map f1 f2 = function
    | Nil -> Nil
    | AbsList id -> AbsList (f2 id)
    | Cons (x,xs) -> Cons (f1 x , map f1 f2 xs)
  let rec map2 f1 = function
    | Nil -> Nil
    | AbsList id -> AbsList id
    | Cons (x,xs) -> Cons (f1 x , map2 f1 xs)
  let rec map3 f1 f2 = function
    | Nil -> Nil
    | AbsList id -> f2 (AbsList id)
    | Cons (x,xs) -> Cons (f1 x , map3 f1 f2 xs)
  let rec iter f1 f2 = function
    | Nil -> ()
    | AbsList id -> f2 id
    | Cons (x,xs) -> f1 x; iter f1 f2 xs
  let rec equal f l1 l2 =
    match l1,l2 with
    | Nil,Nil -> true
    | AbsList i1, AbsList i2 -> i1 = i2
    | Cons (x,xs) , Cons (y,ys) -> if f x y then equal f xs ys else false
    | _ -> false
  let rec replace_trailing_abslist uid_to_replace newls = function
    | Nil -> Nil
    | AbsList uid -> if uid = uid_to_replace then newls else AbsList uid
    | Cons (x,xs) -> Cons (x, replace_trailing_abslist uid_to_replace newls xs)
  let to_list ls =
    let rec aux acc = function
      | Nil -> (List.rev acc),None
      | AbsList uid -> acc,Some uid
      | Cons (x,xs) -> aux (x::acc) xs
    in
    aux [] ls
end

type g_expr = ((ident * Type.t * marker) list) * (((loc * lex_pos_opt) * expression) list) * g_prop
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
  | AbsCon of uniqueId * Type.t * string * marker option
  (* Abstract functions are named objects with a string prefix and a uniqueId to identify them.
   * They also carry their type which is of the form t1 -> t2,
   * where t1 is the first, and t2 is the second Type.t.
   * *)
  | AbsFun of uniqueId * Type.t * Type.t * string * (g_expr option)
  | ListVal of value sym_list * Type.t
  
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
  | TupleProjExp of expression * int * int * lex_pos_opt
  | TupleUpdExp  of expression * int * int * expression * lex_pos_opt
  | MatchExp of Type.t * expression * expression * ident * ident * expression * lex_pos_opt
  (* match (exp:t list) with | [] -> exp | (id1:t) :: (id2:t list) -> exp *)

type relation =
  | Equiv
  | Approx
  | ApproxInv

(* the program is two expressions and their relation *)

type program = {e1:expression; e2:expression; rel:relation * Type.t}

(* convenience functions *)

(* extremely useful string function *)
let string_of_sequence delim f ls = String.concat delim (List.map f ls)
let string_of_list f ls = Printf.sprintf "[%s]" (String.concat ";" (List.map f ls))

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
  | MatchExp (_,_,_,_,_,_, p) -> p

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
  | Implies   -> "=>"
  | Fst       -> "fst"
  | Snd       -> "snd"
  | ListCons  -> "::"
  | PrintOp   -> "_print_"

let string_of_const c =
  match c with
  | IntConst  i -> string_of_int i
  | BoolConst b -> string_of_bool b
  | UnitConst   -> "()"

let rec string_of_gprop = function
  | GConst (c,_) -> string_of_const c
  | GIdent (i,_) -> string_of_id i
  | GArith (op,gs,_) ->
     Printf.sprintf "(%s %s)"
       (string_of_op op)
       (string_of_sequence " " string_of_gprop gs)
  | GAbsCon (i,t,s,_) ->
     Printf.sprintf "(%s%d:%s)"
       s i (Type.string_of_t t)
  | GDeref  (l, p) -> "!" ^ (string_of_loc l)

let rec string_of_gen = function
  | (its, lpes, gprop) ->
     (*((ident * Type.t) list) * (((loc * lex_pos_opt) * expression) list) * g_prop*)
     let its_string =
       string_of_sequence ","
         (fun (i,t,m) ->
           Printf.sprintf "(%s : %s {%d})" (string_of_id i) (Type.string_of_t t) m) its
     in
     let lpes_string =
       string_of_sequence ","
         (fun ((l,_),e) ->
           Printf.sprintf "(%s as %s)" (string_of_loc l) (string_of_exp e)) lpes
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
  | TupleVal (vs) -> Printf.sprintf "(%s)" (iter string_of_val vs)
  | FunVal (fid, ft, param, pt, e, gen) ->
     let gen_string = match gen with None -> "" | Some gen -> (string_of_gen gen) in
     Printf.sprintf "(fix %s. fun %s :(%s -> %s) %s -> %s)"
       (string_of_id fid)
       (string_of_id param)
       (Type.string_of_t pt)
       (Type.string_of_t ft)
       gen_string
       (string_of_exp e)
  | AbsCon (i, t, s, _) -> (** NOTE: keep the marker hidden **)
     Printf.sprintf "(%s%d : %s)"
       s i (Type.string_of_t t)
  | AbsFun  (i, t1, t2, s, gen) ->
     let gen_string = match gen with None -> "" | Some gen -> (string_of_gen gen) in
     Printf.sprintf "(%s%d : %s -> %s %s)"
       s i (Type.string_of_t t1) (Type.string_of_t t2) gen_string
  | ListVal (ls,t) ->
     Printf.sprintf "(%s : %s list)" (SymList.to_string string_of_val ls) (Type.string_of_t t)

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
     Printf.sprintf "(%s %s)"
       (string_of_op op)
       (string_of_sequence " " string_of_exp es)
  | AppExp    (e1, e2, p) ->
     Printf.sprintf "(%s %s)"
       (string_of_exp e1) (string_of_exp e2)
  | CondExp   (e1, e2, e3, p) ->
     Printf.sprintf "(if %s then %s else %s)"
       (string_of_exp e1) (string_of_exp e2) (string_of_exp e3)
  | NewRefExp (l, lt, e1, e2, p) ->
     Printf.sprintf "(ref %s : %s = %s in %s)"
       (string_of_loc l) (Type.string_of_t lt) (string_of_exp e1) (string_of_exp e2)
  | DerefExp  (l, p) -> "!" ^ (string_of_loc l)
  | AssignExp (l, e, p) ->
     Printf.sprintf "(%s := %s)"
       (string_of_loc l) (string_of_exp e)
  | LetExp    (i, it, e1, e2, p) ->
     Printf.sprintf "(let %s : %s = %s in %s)"
       (string_of_id i) (Type.string_of_t it) (string_of_exp e1) (string_of_exp e2)
  | LetTuple  (is_ts, e1, e2, p) ->
     Printf.sprintf "(let (%s) : (%s) = %s in %s)"
       (iter (fun (id, _) -> string_of_id id) is_ts)
       (iter (fun (_, it) -> Type.string_of_t it) is_ts)
       (string_of_exp e1) (string_of_exp e2)
  | SeqExp    (e1, e2, p) ->
     Printf.sprintf "(%s ; %s)"
     (string_of_exp e1) (string_of_exp e2)
  | TupleExp  (es, p) -> Printf.sprintf "(%s)" (iter string_of_exp es)
  | BotExp    p -> "_bot_"
  | TupleProjExp (e1, i, j, p) ->
     Printf.sprintf "(%s [%d / %d])"
       (string_of_exp e1) i j
  | TupleUpdExp  (e1, i, j, e2, p) ->
     Printf.sprintf "(%s [%d / %d := %s])"
       (string_of_exp e1) i j (string_of_exp e2)
  | MatchExp (t,e1,e2,i1,i2,e3,p) ->
     Printf.sprintf "(match %s with [] -> %s | %s :: %s -> %s)"
       (string_of_exp e1)
       (string_of_exp e2)
       (string_of_id i1)
       (string_of_id i2)
       (string_of_exp e3)

let string_of_pgm {e1 = e1; e2 = e2; rel = (r, t)} =
  (string_of_exp e1) ^ "\n" ^ (
    match r with
    | Equiv     -> "|||"
    | Approx    -> "|<|"
    | ApproxInv -> "|>|"
  ) ^ "_" ^ (Type.string_of_t t) ^ "\n" ^
  (string_of_exp e2)

let rec abslist_swap_val id_to new_ls v =
  match v with
  | ListVal(ls,t) ->
     ListVal(SymList.map3
               (abslist_swap_val id_to new_ls)
               (function
                | AbsList id -> if id = id_to then new_ls else AbsList id
                | x -> x) ls, t)
  | ConstVal c -> v
  | TupleVal vs -> TupleVal (List.map (abslist_swap_val id_to new_ls) vs)
  | FunVal (fid, ft, param, pt, e, gen) ->
     FunVal (fid, ft, param, pt, abslist_swap_exp id_to new_ls e, gen)
  | AbsCon (i, t, s, _) -> v
  | AbsFun  (i, t1, t2, s, gen) -> v
and abslist_swap_exp id_to_replace new_symlist exp =
  let aux = (abslist_swap_exp id_to_replace new_symlist) in
  match exp with
  | ValExp (v , p) -> ValExp (abslist_swap_val id_to_replace new_symlist v, p)
  | IdentExp _ | DerefExp _ -> exp
  | ArithExp (op, es, p) -> ArithExp (op, List.map aux es, p)
  | AppExp (e1, e2, p) -> AppExp (aux e1, aux e2, p)
  | CondExp (e1, e2, e3, p) -> CondExp (aux e1, aux e2, aux e3, p)
  | NewRefExp (l, lt, e1, e2, p) -> NewRefExp (l, lt, aux e1, aux e2, p)
  | AssignExp (l, e, p) -> AssignExp (l, aux e, p)
  | LetExp (i, it, e1, e2, p) -> LetExp (i, it, aux e1, aux e2, p)
  | LetTuple (is_ts, e1, e2, p) -> LetTuple (is_ts, aux e1, aux e2, p)
  | SeqExp (e1, e2, p) -> SeqExp (aux e1, aux e2, p)
  | TupleExp (es, p) -> TupleExp (List.map aux es, p)
  | BotExp p -> exp
  | TupleProjExp (e1, i, j, p) -> TupleProjExp (aux e1, i, j, p)
  | TupleUpdExp (e1, i, j, e2, p) -> TupleUpdExp (aux e1, i, j, e2, p)
  | MatchExp (t,e1,e2,i1,i2,e3,p) -> MatchExp (t,aux e1, aux e2,i1,i2, aux e3,p)
