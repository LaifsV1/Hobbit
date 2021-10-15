let y = ref 0 in
let set = fun z
  -> y := z
in
let get = fun ()
  -> !y
in (fun f -> f set get)
