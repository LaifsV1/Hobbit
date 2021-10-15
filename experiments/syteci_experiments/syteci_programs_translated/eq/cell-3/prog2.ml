let mk_cell =
  fun x ->
  let y1 = ref x in
  let y2 = ref x in
  let p = ref 1 in
  let inot x = if x = 0 then 1 else 0 in
  let set = fun z -> p := inot !p;
      if !p = 1 then y1 := z else y2 := z in
  let get = fun () -> if !p = 1 then !y1 else !y2 in
  (fun f -> f set get)
in
mk_cell
