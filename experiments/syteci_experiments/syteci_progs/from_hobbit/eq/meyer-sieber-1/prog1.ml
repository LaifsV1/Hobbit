let rec bot () = bot () in
let mod = (fun x -> fun y -> (x - ((x / y) * y))) in
fun g ->
  let x = ref 0 in
  let f = fun () -> x := !x + 2
  in ((g f) ;
      if (mod !x 2 = 0) then () else bot ())
