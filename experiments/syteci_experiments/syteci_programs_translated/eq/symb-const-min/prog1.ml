let rec bot () = bot () in
fun b ->
  if b then bot ()
  else 1
