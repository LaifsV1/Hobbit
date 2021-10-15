fun n ->
  let rec aux m res =
     if (m <= 1) then res
     else aux (m-1) (m * res)
  in aux n 1
