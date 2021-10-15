fun n ->
  let res = ref 1 in
  let rec aux m =
     if (m <= 1) then ()
     else res := !res*m; aux (m-1)
  in aux n; !res
