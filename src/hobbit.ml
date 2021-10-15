open Lexing
open Lexer
open Z3api

 (* report_error: string -> lexbuf -> string -> unit
Fucntion printing an error
Parameters:
  - filename: path of the file 
  - lexbuf: lexer buffer
  - msg: message to print
*)
let report_error filename lexbuf msg =
  let (b,e) = (lexeme_start_p lexbuf, lexeme_end_p lexbuf) in
  let fc = b.pos_cnum - b.pos_bol + 1 in
  let lc = e.pos_cnum - b.pos_bol + 1 in
  Printf.eprintf "File \"%s\", line %d, characters %d-%d: %s\n" filename b.pos_lnum fc lc msg

let debug = ref ""
let inputFile = ref "<stdin>"
let bound = ref 6
let traversal = ref 0
let maxpending = ref 1000000
let which_lts = ref 0
let lts_kinds = [("immutable list"); ("queue and stack"); ("list ref"); ("stackless")]
let get_lts_kind n =
  match List.nth_opt lts_kinds n with
  | None -> failwith "Error: invalid LTS option chosen"
  | Some s -> s

(* up-to *)
let maxremembered = ref 10000
let upto_techs = ref "ngsrialfzue"

let parse_debug str =
  let contains c = String.contains str c in
  let y = contains 'y' in
  let t = contains 't' in
  let c = contains 'c' in
  let b = contains 'b' in
  let m = contains 'm' in
  let n = contains 'n' in
  let g = contains 'g' in
  let s = contains 's' in
  let r = contains 'r' in
  let i = contains 'i' in
  let a = contains 'a' in
  let l = contains 'l' in
  let f = contains 'f' in
  let z = contains 'z' in
  let u = contains 'u' in
  let e = contains 'e' in
  (y,t,c,b,m,n,g,s,r,i,a,l,f,z,u,e)

let parse_upto str =
  let contains c = String.contains str c in
  let n = contains 'n' in
  let g = contains 'g' in
  let s = contains 's' in
  let r = contains 'r' in
  let i = contains 'i' in
  let a = contains 'a' in
  let l = contains 'l' in
  let f = contains 'f' in
  let z = contains 'z' in
  let u = contains 'u' in
  let e = contains 'e' in
  (n,g,s,r,i,a,l,f,z,u,e)


let main =
begin

  let def_msg_s = Printf.sprintf "%s (default: %s)" in
  let def_msg_i msg i = def_msg_s msg (string_of_int i) in
  let speclist = [("-d", Arg.Set_string debug,
                   (def_msg_s "debug mode: e.g. \"ytcemngsrialfzu\" for t[y]pe-checking [t]races [c]onfigurations sym[b]olic-environment [m]emoisation [n]ormalisation [g]arbage-collection up-to-[s]eparation up-to-name-[r]euse up-to-[i]dentity sigma-g[a]rbage-collection sigma-norma[l]isation sigma-simpli[f]ication generali[z]ation remove-gamma-d[u]plicates up-to-re[e]ntry" !debug));
                  ("-i", Arg.Set_string (inputFile),
                   (def_msg_s "input file" !inputFile));
                  ("-l", Arg.Set_int (which_lts),
                   (def_msg_i "LTS implementation: 0 = immutable list" !which_lts));
                  ("-b", Arg.Set_int (bound),
                   (def_msg_i "bound for function applications" !bound));
                  ("-t", Arg.Set_int (traversal),
                   (def_msg_i "LTS traversal mode: 0 = BFS / 1 = DFS" !traversal));
                  ("-p", Arg.Set_int maxpending,
                   (def_msg_i "max number of pending configurations allowed" !maxpending));
                  ("-m", Arg.Set_int (maxremembered),
                   (def_msg_i "memoisation cache size (max no. of configurations remembered), size 0 turns off memoisation, normalisation and garbage collection" !maxremembered));
                  ("-u", Arg.Set_string (upto_techs),
                   (def_msg_s "up-to techniques: e.g. \"ngsrialfzue\" for [n]ormalisation [g]arbage-collection up-to-[s]eparation up-to-name-[r]euse up-to-[i]dentity sigma-g[a]rbage-collection sigma-norma[l]isation sigma-simpli[f]ication generali[z]ation remove-gamma-d[u]plicates up-to-re[e]ntry" !upto_techs))
                 ] in
  let usage_msg = "Equivalence Checking Tool" in
  Arg.parse speclist print_endline usage_msg;
  print_endline "****************";
  Printf.printf "Debug mode: %s\n" !debug;
  Printf.printf "Input file: %s\n" !inputFile;
  Printf.printf "LTS implementation: %s\n" (get_lts_kind !which_lts);
  Printf.printf "Bound: %d\n"      !bound;
  Printf.printf "Traversal: %s\n" (if !traversal = 0 then "BFS" else "DFS");
  Printf.printf "Max Pending Confs: %d\n" !maxpending;
  Printf.printf "Memoisation%s \n" (if !maxremembered = 0 then ": off"
                                    else Printf.sprintf " cache size: %d" !maxremembered);
  Printf.printf "Up-to techniques: %s\n" !upto_techs;
  print_endline "****************";
  
  (* Opening the file *)
  let input = if (!inputFile = "<stdin>") then stdin else open_in !inputFile in
  (* Lexing *)
  let filebuf = Lexing.from_channel input in
  try
    (* Parsing *)
    let pgm = Parser.main Lexer.token filebuf  in
    (if !debug <> "" then print_endline "[parsing] File parsed");
    let pgm = Preprocess.assign_fresh_ids_to_names_pgm pgm in
    (if !debug <> "" then print_endline ("Program: \n" ^ (Ast.string_of_pgm pgm)));
    let pgm = Typing.type_pgm pgm (String.contains !debug 'y') in
    (if !debug <> "" then
       begin
         print_endline "[typing] File typed";
         print_endline ("Type: \n" ^ (Type.string_of_t (snd pgm.rel)));
         print_endline ("[z3] Z3 check sat: ");
         let z3_test = (check_sat ((_int 42) ==. ((_sint "x") +. (_sint "y")))) in
         assert(z3_test);
         print_endline (string_of_bool z3_test);
         print_endline ("[z3] Z3 model:");
         let z3_model_test = (get_model_s ()) in
         print_endline (z3_model_test)
       end);
    (match !which_lts with
     | 0 -> Lts.start_bisim_game pgm.e1 pgm.e2 !bound (parse_debug !debug) !traversal !maxpending !maxremembered (parse_upto !upto_techs)
     | n -> failwith (Printf.sprintf "selected invalid LTS kind %d" n))

  with
   | Parser.Error -> Error.report_error_f_lex !inputFile (Lexer.get_lex_start_end_p filebuf) "Parsing Error."
   | Error.LexE (lex_pos, m)
   | Error.ParseE (lex_pos, m) -> Error.report_error_f_lex !inputFile lex_pos ("Parsing Error: " ^ m)
   | Error.SyntaxE (lex_pos_opt, m)
   | Error.TypeE (lex_pos_opt, m)
   | Error.RuntimeE (lex_pos_opt, m) -> begin
       match lex_pos_opt with
       | None -> Error.report_error_f !inputFile ("Typing Error: " ^ m)
       | Some lex_pos -> Error.report_error_f_lex !inputFile lex_pos ("Typing Error: " ^ m)
   end


end
 
let () = main
