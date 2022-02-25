let rec bot () = bot () in
fun (f : Unit->Unit) -> f (fun () -> bot ())

