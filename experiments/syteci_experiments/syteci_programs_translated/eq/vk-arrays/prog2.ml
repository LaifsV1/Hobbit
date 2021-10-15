let rev = fun ar -> fun i -> if 0<=i then if i<10 then ar (9-i) else 0 else 0 
in fun ar -> rev (rev ar)
