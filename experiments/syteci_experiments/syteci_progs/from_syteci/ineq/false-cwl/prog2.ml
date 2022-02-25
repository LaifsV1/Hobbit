let x = ref 0 in
let inc f = let n = !x in  f(); x:= n+1 in
let get () = !x in (inc,get)
