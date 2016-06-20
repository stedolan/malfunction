open Malfunction_parser
open Malfunction_interpreter

exception ReifyFailure of string
let rec reify = function
| Block (n, xs) -> reify_block n xs
| Seq (`Array, _, xs) -> reify_block 0 xs
| Seq (`Bytevec, _, xs) ->
   let to_char = function
     | Int (`Int n) when 0 <= n && n < 256 ->
        String.make 1 (Char.chr n)
     | _ -> raise (ReifyFailure "reify: noncharacter in string") in
   Obj.repr (String.concat "" (List.map to_char (Array.to_list xs)))
| Int n -> Obj.(match n with
  | `Int n -> repr n
  | `Int32 n -> repr n
  | `Int64 n -> repr n
  | `Bigint n -> repr n)
| Func _ -> raise (ReifyFailure "reify: functional value")

and reify_block n xs =
  let o = Obj.new_block n (Array.length xs) in
  Array.iteri (Obj.set_field o) (Array.map reify xs);
  o

let check xs =
  Array.iter (fun a ->
  Pervasives.print_char 
    (if Pervasives.(=) (Marshal.from_channel Pervasives.stdin) a then
        'Y'
     else
        'N')) xs;
  Pervasives.flush_all ()

let check_stub = "
  (lambda ($xs)
    (seq
      (apply (global $Array $iter) (lambda ($x)
        (apply (global $Pervasives $print_char)
          (if (apply (global $Pervasives $=)
                     $x 
                     (apply (global $Marshal $from_channel) (global $Pervasives $stdin)))
              89
              78))) $xs)
      (apply (global $Pervasives $print_newline) 0)))"

type test_result =
  [ `Bad_test of string (* expected output had undefined behaviour or was a function *)
  | `Undefined of string (* testcase had undefined behaviour *)
  | `Crash of string (* compiled executable failed to run or crashed, even though testcase had defined behaviour *)
  | `Different (* interpreter and compiler agree that testcase does not match expected output *)
  | `Inconsistent (* interpreter and compiler disagree whether testcase matches expected output *)
  | `Match ] (* interpreter and compiler agree that testcase matches expected output *)


exception HarnessFailed of string
let compile cases =
  let checker = Malfunction_parser.read_expression
    (Lexing.from_string check_stub) in
  let cases = cases |> List.map @@ function
    | `Bad_test _ | `Undefined _ -> Mint (`Int 0)
    | `Match (test, _) | `NoMatch (test, _) -> test in
  let code =
    Mmod ([`Unnamed (Mapply (checker, [Mblock (0, cases)]))], []) in
  try
    code
    |> Malfunction_compiler.module_to_lambda
    |> Malfunction_compiler.lambda_to_cmx "test" "test"
    |> Malfunction_compiler.link_executable "test"
    |> (function 0 -> () | _ -> raise (HarnessFailed "Link error"))
  with
    e -> 
      Location.report_exception Format.str_formatter e;
      raise (HarnessFailed (Format.flush_str_formatter ()))

let try_run_tests cases =
  compile cases;
  let (rd, wr) = Unix.open_process "./test" in
  cases 
  |> List.map (function
    | `Bad_test _ | `Undefined _ -> Obj.repr 0
    | `Match (_, obj) | `NoMatch (_, obj) -> obj)
  |> List.iter (fun x -> Marshal.to_channel wr x []);
  let answer = input_line rd in
  match Unix.close_process (rd, wr) with
  | Unix.WEXITED 0 when String.length answer = List.length cases ->
     cases |> List.mapi (fun i c -> match c, answer.[i] with
     | (`Bad_test _ | `Undefined _) as x, _ -> x
     | `Match _, 'Y' -> `Match
     | `NoMatch _, 'N' -> `Different
     | `Match _, 'N' -> `Inconsistent
     | `NoMatch _, 'Y' -> `Inconsistent
     | _, c -> `Crash ("output produced '" ^ String.make 1 c ^ "'"))
  | _ -> raise (HarnessFailed "executable failed")

let run_tests cases =
  try
    try_run_tests cases
  with
    (* failed to run all at once, run them one at a time to isolate crashing case *)
    HarnessFailed _ ->
      cases |> List.map @@ fun x ->
        try List.hd (try_run_tests [x]) with
          HarnessFailed s -> `Crash s

let test cases =
  cases
  |> List.map (fun (test, expect) ->
    match eval expect with
    | exception (Error s) -> `Bad_test s
    | expectRes -> match eval test, reify expectRes with
      | exception (Error s) -> `Undefined s
      | exception (ReifyFailure s) -> `Bad_test s
      | testRes, expectObj when testRes <> expectRes -> `NoMatch (test, expectObj)
      | testRes, expectObj -> `Match (test, expectObj))
  |> run_tests
