
let readMAX = ref 100 in
let read1 =
  (fun () -> readMAX := !readMAX -1;
            true)
in
let read2 =
  (fun () -> readMAX := !readMAX -1;
            true)
in
let read3 =
  (fun () -> readMAX := !readMAX -1;
            true)
in
let read4 =
  (fun () -> readMAX := !readMAX -1;
            true)
in
let read5 =
  (fun () -> readMAX := !readMAX -1;
            true)
in

read1
