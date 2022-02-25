let x = ref 0 in 
let inc () = x:=!x-1 in
let get () = 0-(!x) in
(inc,get)

