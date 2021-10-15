
let funds = ref 10 in
let withdraw1 =
 (fun send1 -> (if not(!funds < 1)
                then (funds := !funds - 1; send1 ())
                else ());
                !funds)
in withdraw1
