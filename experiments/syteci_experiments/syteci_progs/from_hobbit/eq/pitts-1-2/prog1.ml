let a = ref 0 in
fun x -> (a := !a + x ; !a)
