type t = 
  | UnitT
  | BoolT
  | IntT
  | FunT of t list * t (* convenient for typing basic operators that may have two items *)
  | TupleT of t list
  | VarT of t option ref

let gen_type () = VarT(ref None)

let rec string_of_t = function
  | UnitT -> "Unit"
  | BoolT -> "Bool"
  | IntT -> "Int"
  | FunT (ts, t2) -> 
      "(" ^ (List.fold_left (fun str ty -> (if str = "" then str else str ^ " * ") ^ (string_of_t ty)) "" ts)
      ^ "->" ^ (string_of_t t2) ^ ")"
  | TupleT tlst -> "(" ^ (List.fold_right (fun t str -> (string_of_t t) ^ (if str = "" then "" else ", ") ^ str) tlst "") ^ ")"
  | VarT tref -> begin
      match !tref with
      | None -> "?" 
      | Some t -> string_of_t t
  end

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
let rec compare t1 t2 =
  if t1 = t2 then 0
  else
    let rec aux =
      function
      | [],[] -> 0
      | x::xs , [] -> 1
      | [] , x::xs -> -1
      | x::xs , y::ys ->
         let c = compare x y in
         match c with
         | 0 -> aux(xs,ys)
         | _ -> c
    in
    begin
      match t1,t2 with
      | UnitT , _ -> -1
      | BoolT , UnitT -> 1
      | BoolT , _ -> -1
      | IntT , UnitT | IntT , BoolT -> 1
      | IntT , _ -> -1
      | FunT _ , UnitT | FunT _ , BoolT | FunT _ , IntT -> 1
      | FunT (ts1,t1) , FunT (ts2,t2) ->
         let c = compare t1 t2 in
         if c = 0 then
           begin
             aux (ts1,ts2)
           end
         else c
      | FunT _ , _ -> -1
      | TupleT _ , UnitT | TupleT _ , BoolT | TupleT _ , IntT | TupleT _ , FunT _ -> 1
      | TupleT ts1 , TupleT ts2 ->
         begin
           aux (ts1,ts2)
         end
      | TupleT _ , _ -> -1
      | VarT _ , _ -> 1
    end
