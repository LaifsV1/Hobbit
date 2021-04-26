
exception LexE of (Lexing.position * Lexing.position) * string
exception ParseE of (Lexing.position * Lexing.position) * string
exception SyntaxE of (Lexing.position * Lexing.position) option * string
exception TypeE of (Lexing.position * Lexing.position) option * string
exception RuntimeE of (Lexing.position * Lexing.position) option * string

let report_error_f fn m =
  Printf.eprintf "\n\x1b[1;31mERROR!\x1b[0m %s: %s" fn m;
  exit 1

 
let report_error_f_lex fn (bp, ep) m =
  let bc = bp.Lexing.pos_cnum - bp.pos_bol + 1 in
  let ec = ep.Lexing.pos_cnum - bp.pos_bol + 1 in
  if (bp.pos_lnum = ep.pos_lnum) then
    report_error_f fn (Printf.sprintf "%d.%d-%d: %s\n" bp.pos_lnum bc ec m)
  else
    report_error_f fn (Printf.sprintf "%d.%d-%d.%d: %s\n" bp.pos_lnum bc bp.pos_lnum ec m)

let failwith_lex_opt p m =
  match p with
  | None -> failwith m
  | Some (bp,ep) ->
     let bc = bp.Lexing.pos_cnum - bp.pos_bol + 1 in
     let ec = ep.Lexing.pos_cnum - bp.pos_bol + 1 in
     if (bp.pos_lnum = ep.pos_lnum) then
       failwith (Printf.sprintf "%d.%d-%d: %s"
                   bp.pos_lnum bc ec m)
     else
       failwith (Printf.sprintf "%d.%d-%d.%d: %s"
                   bp.pos_lnum bc bp.pos_lnum ec m)

let report_error_lex p m =
  match p with
  | None -> print_endline m; exit 1;
  | Some (bp,ep) ->
     let bc = bp.Lexing.pos_cnum - bp.pos_bol + 1 in
     let ec = ep.Lexing.pos_cnum - bp.pos_bol + 1 in
     if (bp.pos_lnum = ep.pos_lnum) then
       (print_endline (Printf.sprintf "Error: %d.%d-%d: %s"
                         bp.pos_lnum bc ec m); exit 1)
     else
       (print_endline (Printf.sprintf "Error: %d.%d-%d.%d: %s"
                         bp.pos_lnum bc bp.pos_lnum ec m); exit 1)
