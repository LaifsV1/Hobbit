let x = ref 0 in
let rec call f =
  x := !x + 1;
  f ();
  x := !x - 1;
  !x < 100
in
call
