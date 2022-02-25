fun u ->
  let (f,v) = u in
  let (n,x) = v in
  let r = ref x in
  let rec aux m =
    if (m <= 0) then ()
    else r := f !r; aux (m-1)
   in aux n; !r
