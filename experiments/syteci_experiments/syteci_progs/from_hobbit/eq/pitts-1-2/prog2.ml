let b = ref 0 in
fun y -> (b := !b - y ; 0 - !b)
