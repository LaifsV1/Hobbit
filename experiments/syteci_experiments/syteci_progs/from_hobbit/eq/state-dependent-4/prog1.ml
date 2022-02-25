let rec bot () = bot () in
fun f -> 
  let l1 = ref 0 in
  let l2 = ref 0 in
  f (fun () -> if !l1 = 1 then bot () else l2 := 1);
  if !l2 = 1 then bot () else l1 := 1
