type t = 
  | UnitT
  | BoolT
  | IntT
  | FunT of t list * t (* convenient for typing basic operators that may have two items *)
  | TupleT of t list
  | VarT of t option ref
  | ListT of t

let gen_type () = VarT(ref None)

let rec string_of_t = function
  | UnitT -> "unit"
  | BoolT -> "bool"
  | IntT -> "int"
  | FunT (ts, t2) -> 
     "(" ^ (List.fold_left
              (fun str ty -> (if str = "" then str else str ^ " * ") ^ (string_of_t ty)) "" ts)
      ^ "->" ^ (string_of_t t2) ^ ")"
  | TupleT tlst ->
     "(" ^ (List.fold_right
              (fun t str -> (string_of_t t) ^ (if str = "" then "" else ", ") ^ str) tlst "") ^ ")"
  | VarT tref ->
     begin
       match !tref with
       | None -> "?"
       | Some t -> Printf.sprintf "VarT(%s)" (string_of_t t)
     end
  | ListT t -> Printf.sprintf "%s list" (string_of_t t)

(********************************
 * order: (smallest -> largest) *
 * - unit                       *
 * - bool                       *
 * - int                        *
 * - fun                        *
 * - tuple                      *
 * - var                        *
 ********************************)
(************************************
 * Fun(ts1,t1) > Fun(ts2,t2)        *
 * if t1 > t2 otherwise             *
 * if ts1 > ts2                     *
 * where ts1 > ts2                  *
 * if length ts1 > length ts2       *
 * otherwise if head ts1 > head ts2 *
 * otherwise if tail ts1 > tail ts2 *
 ************************************)
let compare t1 t2 = compare t1 t2
