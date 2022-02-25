let x = ref 0 in 
let b = ref 0 in
let inc f = if !b = 0 then b:=1;let n = !x in  f(); x:= n+1;b:=0 else () in
let get () = !x
in (inc,get)
