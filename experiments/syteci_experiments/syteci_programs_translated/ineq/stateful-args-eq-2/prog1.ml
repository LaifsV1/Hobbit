let x = ref 0 in
(fun f ->
 (f (fun () -> x := !x + 2);
  !x = 10))
