let x = ref 0 in 
let inc () = x:=!x+1 in
let get () = !x in
(inc,get)
