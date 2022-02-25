let x = ref 0 in
let rec call f =
  x := !x + 1;
  f ();
  x := !x - 1;
  true
in
call
