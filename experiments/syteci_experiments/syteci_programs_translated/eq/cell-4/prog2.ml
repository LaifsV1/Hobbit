let y1 = ref 0 in
let y2 = ref 0 in
let p = ref 0 in
let mod = (fun x -> fun y -> (x - ((x / y) * y))) in
let set1 = fun z 
  -> p := !p + 1; if mod !p 2 = 0 then y1 := z else y2 := z
in
let get1 = fun () 
  -> if mod !p 2 = 0 then !y1 else !y2
in (fun f -> f set1 get1)
