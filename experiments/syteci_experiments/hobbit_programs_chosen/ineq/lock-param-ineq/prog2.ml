
let readMAX = ref 30 in
let read =
  (fun () -> readMAX := !readMAX -1;
            true)
in read
