fun b ->
  if b=0 then (fun () -> true)
    else (fun () -> false)
