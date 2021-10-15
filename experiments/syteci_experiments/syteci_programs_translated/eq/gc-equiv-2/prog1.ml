let f = ref (fun () -> ()) in
fun () -> let l = ref () in
f := (fun () -> !l); !f ()
