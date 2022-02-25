let is_even = ref 1 in
let x = ref 0 in
let call_even =
  fun () ->
  (if !is_even = 1 then x := !x + 1
   else ());
  is_even := 0;
  !x < 5
in
let call_odd =
  fun () ->
  (if !is_even = 1 then ()
   else x := !x + 1);
  is_even := 1;
  !x < 5
in
(fun f -> f call_even call_odd)
