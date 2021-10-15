let x = ref 0 in
(fun f ->
 (f (fun () -> x := !x + 1);
  !x = (0-2)))
