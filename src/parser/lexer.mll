{
  open Parser
  open Lexing

  let get_lex_pos lexbuf = 
    let (b,e) = (lexeme_start_p lexbuf, lexeme_end_p lexbuf) in
    let line_no = b.pos_lnum in
    let char_start = b.pos_cnum - b.pos_bol + 1 in
    let char_end = e.pos_cnum - b.pos_bol + 1 in
    (line_no, char_start, char_end)
 
  let get_lex_start_end_p lexbuf = (lexeme_start_p lexbuf, lexeme_end_p lexbuf)
}


let digit = ['0'-'9']
let lowercase = ['a' - 'z']
let uppercase = ['A' - 'Z']
let alphabet = lowercase | uppercase
let alphanum = alphabet | digit | '_'
let alphanum_extended = alphanum | ' ' | ':' | ',' | '.' | '(' | ')' | '&' | '%' | ';' | '{' | '}' | '[' | ']' | '?' | '=' | '+' | '*' | '^' | '!' | '@' | '<' | '>' | '$' | '|' | '/' | '-'
let id = alphabet alphanum*
let char = '\'' alphanum? '\''
let string = '"' alphanum_extended* '"'
let comments =
  (* Comments end of line *)
  "#" [^'\n']*
let open_comment = "(*"
let close_comment = "*)"
let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"

rule token = parse
  | newline   { new_line lexbuf; token lexbuf } (* ignore newlines but count them *)
  | white     { token lexbuf }                  (* ignore whitespaces and tabs *)    
  | comments  { (token lexbuf) }
  | '_'       {UNDERSCORE (get_lex_start_end_p lexbuf)}
  | '('       {LPAREN (get_lex_start_end_p lexbuf)}
  | ')'       {RPAREN (get_lex_start_end_p lexbuf)}
  | '{'       {LBRACE (get_lex_start_end_p lexbuf)}
  | '}'       {RBRACE (get_lex_start_end_p lexbuf)}
  | '['       {LBRACKET (get_lex_start_end_p lexbuf)}
  | ']'       {RBRACKET (get_lex_start_end_p lexbuf)}
  | "="       {EQUAL (get_lex_start_end_p lexbuf)}
  | "=="      {EQUAL (get_lex_start_end_p lexbuf)}
  | ":="      {COLONEQUAL (get_lex_start_end_p lexbuf)}
  | "!"       {BANG (get_lex_start_end_p lexbuf)}
  | "<>"      {NEQUAL (get_lex_start_end_p lexbuf)}
  | ';'       {SEMI (get_lex_start_end_p lexbuf)}
  | ','       {COMMA (get_lex_start_end_p lexbuf)}
  | '<'       {LESS (get_lex_start_end_p lexbuf)}
  | '>'       {GREATER (get_lex_start_end_p lexbuf)}
  | "<="      {LESSEQ (get_lex_start_end_p lexbuf)}
  | ">="      {GREATEREQ (get_lex_start_end_p lexbuf)}
  | "==>"     {IMPLIES (get_lex_start_end_p lexbuf)}
  | '+'       {PLUS (get_lex_start_end_p lexbuf)}
  | '-'       {MINUS (get_lex_start_end_p lexbuf)}
  | '*'       {TIMES (get_lex_start_end_p lexbuf)}
  | '/'       {DIV (get_lex_start_end_p lexbuf)}
  | "mod"     {MOD (get_lex_start_end_p lexbuf)}
  | "&&"      {AND (get_lex_start_end_p lexbuf)}
  | "||"      {OR (get_lex_start_end_p lexbuf)}
  | '|'       {PIPE (get_lex_start_end_p lexbuf)}
  | "->"      {ARROW (get_lex_start_end_p lexbuf)}
  | "fun"     {FUN (get_lex_start_end_p lexbuf)}
  | "if"      {IF (get_lex_start_end_p lexbuf)}
  | "then"    {THEN (get_lex_start_end_p lexbuf)}
  | "else"    {ELSE (get_lex_start_end_p lexbuf)}
  | "let"     {LET (get_lex_start_end_p lexbuf)}
  | "rec"     {REC (get_lex_start_end_p lexbuf)}
  | "in"      {IN (get_lex_start_end_p lexbuf)}
  | "true"    {TRUE (get_lex_start_end_p lexbuf)}
  | "false"   {FALSE (get_lex_start_end_p lexbuf)}
  | "ref"     {REF (get_lex_start_end_p lexbuf)}
  | "not"     {NOT (get_lex_start_end_p lexbuf)}
  | "fst"     {FST (get_lex_start_end_p lexbuf)} 
  | "snd"     {SND (get_lex_start_end_p lexbuf)}
  | "_bot_"   {BOT (get_lex_start_end_p lexbuf)}
  | "begin"   {BEGIN (get_lex_start_end_p lexbuf)}
  | "end"     {END (get_lex_start_end_p lexbuf)}
  | "as"      {AS (get_lex_start_end_p lexbuf)}
  | "|||"     {EQUIV (get_lex_start_end_p lexbuf)}
  | "|<|"     {APPROX (get_lex_start_end_p lexbuf)}
  | "|>|"     {APPROXINV (get_lex_start_end_p lexbuf)}
  | "unit"    {UNIT (get_lex_start_end_p lexbuf)} 
  | "bool"    {BOOL (get_lex_start_end_p lexbuf)} 
  | "int"     {INT (get_lex_start_end_p lexbuf)} 
  | digit+ as inum
              {NUMBER (((get_lex_start_end_p lexbuf)),(int_of_string inum))}
(*
  | char as text
              {CharValueToken ((get_lex_start_end_p lexbuf),(String.sub text 1 1))}
  | string as text
              {StringValueToken ((get_lex_start_end_p lexbuf),(String.sub text 1 ((String.length text) - 2)))}
*)
  | id as text  {IDENT ((get_lex_start_end_p lexbuf),text)}
  | eof         { EOF (get_lex_start_end_p lexbuf)}
  | open_comment    { comment lexbuf } (* OCaml comments *)
  | _               { raise (Error.LexE (get_lex_start_end_p lexbuf, "Unexpected char: " ^ (Lexing.lexeme lexbuf))) }
and comment = parse
  | close_comment   { token lexbuf }
  | newline         { new_line lexbuf; comment lexbuf }
  | _               { comment lexbuf }
