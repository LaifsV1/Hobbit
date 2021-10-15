let rec bot () = bot () in
fun b ->
  if not(b) then 1
  else bot ()
