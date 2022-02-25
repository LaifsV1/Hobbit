let mk_cell =
  fun x -> 
  let y = ref x in
  let set = fun z -> y := z in
  let get = fun () -> !y in
  (fun f -> f set get)
in
mk_cell
