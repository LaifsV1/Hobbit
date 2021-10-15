let x = ref 0 in
let call_even =
  fun () ->
  (if ((!x - ((!x / 2) * 2)) = 0) then x := !x + 1
   else ());
  !x < 5
in
let call_odd =
  fun () ->
  (if ((!x - ((!x / 2) * 2)) = 0) then ()
   else x := !x + 1);
  !x < 5
in
(fun f -> f call_even call_odd)
