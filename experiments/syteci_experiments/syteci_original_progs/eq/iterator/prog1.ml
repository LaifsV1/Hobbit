fix iterator u ->
  let (f,v) = u in
  let (n,x) = v in
  if n <= 0 then x
  else let y = f x in iterator (f,(n-1,y))
