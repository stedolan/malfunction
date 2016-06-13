{
type sexp =
  (Lexing.position * Lexing.position) * rawsexp
and rawsexp =
| Atom of string
| Var of string
| String of string
| Int of int
| List of sexp list

let loc lexbuf x = ((lexbuf.Lexing.lex_start_p, lexbuf.Lexing.lex_curr_p), x)
let fail lexbuf s = raise (Malfunction.SyntaxError ((lexbuf.Lexing.lex_start_p, lexbuf.Lexing.lex_curr_p), s))

let const_int s =
  match int_of_string s with
  | n -> Int n
  | exception (Failure _) ->
     (* large integers are represented as atoms *)
     Atom s

let var s =
  assert (s.[0] = '$');
  Var (String.sub s 1 (String.length s - 1))

let rec print_sexp ppf (_, s) = let open Format in match s with
  | Atom s -> fprintf ppf "%s" s
  | Var s -> fprintf ppf "$%s" s
  | Int n -> fprintf ppf "%d" n
  | String s -> fprintf ppf "%S" s
  | List l ->
     fprintf ppf "@[<2>(%a)@]" (pp_print_list ~pp_sep:pp_print_space print_sexp) l
}

let space = [' ' '\t' '\r']*

let symbol = ['.' '&' '|' '+' '-' '!' '@' '#' '%' '^' '*' '~' '?' '{' '}' '<' '>' '=']

let atomsymbol = ['+' '-' '<' '>']
let letter = ['a'-'z' 'A'-'Z' '_']
let digit = ['0' - '9']

let atom = (letter | digit | symbol)*
let var = (['a'-'z' 'A'-'Z' '_' '0'-'9' '$'] | symbol)+

let int = ['1'-'9'] ['0'-'9']* | '0'

let string = '"' ([^ '\\' '"']* | ('\\' _))* '"'

(* FIXME: exceptions in int and str cases *)
rule sexps acc = parse
| ')'
  { List.rev acc }
| '('
  { sexps (loc lexbuf (List (sexps [] lexbuf)) :: acc) lexbuf }
| string
  { sexps (loc lexbuf (String (Scanf.sscanf (Lexing.lexeme lexbuf) "%S%!" (fun x -> x))) :: acc) lexbuf }
| int
  { sexps (loc lexbuf (const_int (Lexing.lexeme lexbuf)) :: acc) lexbuf }
| '$' var
  { sexps (loc lexbuf (var (Lexing.lexeme lexbuf)) :: acc) lexbuf }
| atom
  { sexps (loc lexbuf (Atom (Lexing.lexeme lexbuf)) :: acc) lexbuf }
| '\n'
  { Lexing.new_line lexbuf; sexps acc lexbuf }
| space
  { sexps acc lexbuf }
| eof
  { fail lexbuf "Unexpected end of file" }
| _
  { fail lexbuf ("Lexical error on " ^ (Lexing.lexeme lexbuf)) }

and read_only_sexp = parse
| space* '('
  { read_sexp_end (sexps [] lexbuf) lexbuf }
| _
  { fail lexbuf "File must begin with '('" }

and read_sexp_end s = parse
| (space | '\n')* eof
  { loc lexbuf (List s) }
| _
  { fail lexbuf "File contains data past end of sexp" }

and read_next_sexp = parse
| space* '('
  { loc lexbuf (List (sexps [] lexbuf)) }
| _
  { fail lexbuf "Sexp must start with '('" }
