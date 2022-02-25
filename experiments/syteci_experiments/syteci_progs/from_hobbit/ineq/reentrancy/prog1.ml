
let funds = ref 10 in
let withdraw1 =
 (fun send1 -> (if not(!funds < 1)
                then (send1 (); funds := !funds - 1)
                else ());
                !funds)
in withdraw1
