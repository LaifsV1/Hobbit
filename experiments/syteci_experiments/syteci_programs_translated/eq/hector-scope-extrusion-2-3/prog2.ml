fun f ->
f ( fun y -> let x = ref 0 in (if !x = 0 then x := y else x := y - 1) ; !x )
