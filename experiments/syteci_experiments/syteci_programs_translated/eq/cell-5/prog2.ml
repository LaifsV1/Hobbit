let y1 = ref 0 in
let y2 = ref 0 in
let mod = (fun x -> fun y -> (x - ((x / y) * y))) in
let set = fun z
  -> if mod z 2 = 0 then y1 := z else (y1 := 1; y2 := z) in
let get = fun () 
  -> if mod !y1 2 = 0 then !y1 else !y2 in
(fun f -> f set get)
