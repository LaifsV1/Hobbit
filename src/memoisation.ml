
let make_hashtbl n = Hashtbl.create ~random:false n
let make_array n x = Array.make n x

(* size bounded set = 3-tuple record:
   - nxt_idx: index of next free index in the set--ranges from 0 to idx_tbl.length-1;
   - idx_arr: dictionary from indexes to elements--used for constant access to oldest element;
   - mem_tbl: hashtable records whether an element is in the set--used for constant membership access.*)
type 'a size_bounded_set = {mutable nxt_idx: int;
                            mutable idx_arr: 'a array;
                            mutable mem_tbl: ('a,unit) Hashtbl.t}

(* initialises set of size n with first element e *)
let make_bounded_set : int -> 'a -> 'a size_bounded_set =
  fun n dummy ->
  let new_htbl = make_hashtbl n in (* question: what should we initialise with? *)
  {nxt_idx = 0;
   idx_arr = make_array n dummy;
   mem_tbl = new_htbl}

let add : 'a size_bounded_set -> 'a -> bool =
  fun bset conf -> 
  match Hashtbl.find_opt bset.mem_tbl conf with
  | None   ->
     begin
       let nxt =
         if bset.nxt_idx < (Array.length bset.idx_arr)
         then bset.nxt_idx else bset.nxt_idx - (Array.length bset.idx_arr)
       in
       Hashtbl.remove bset.mem_tbl (bset.idx_arr.(nxt));
       bset.nxt_idx <- nxt + 1;
       bset.idx_arr.(nxt) <- conf;
       Hashtbl.add bset.mem_tbl conf ()
     end;
     true
  | Some _ -> false

let mem : 'a size_bounded_set -> 'a -> bool =
  fun bset conf -> Hashtbl.mem bset.mem_tbl conf

