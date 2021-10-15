let x = ref 0 in
fun f -> x:=0; f(); x:=!x+1; f(); !x
