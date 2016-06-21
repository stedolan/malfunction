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

let exec_name = "malfunction_test_exec"

let try_run_tests cases =
  if Sys.file_exists exec_name then
    raise (HarnessFailed ("file exists: "^exec_name));
  let checker = Malfunction_parser.read_expression
    (Lexing.from_string check_stub) in
  let testcases = cases |> List.map @@ function
    | `Bad_test _ | `Undefined _ -> Mint (`Int 0)
    | `Match (test, _) | `NoMatch (test, _) -> test in
  let code =
    Mmod ([`Unnamed (Mapply (checker, [Mblock (0, testcases)]))], []) in
  let temps = ref None in
  let delete_temps () =
    Misc.remove_file exec_name;
    match !temps with Some t -> Malfunction_compiler.delete_temps t | None -> () in
  begin match
    code
    |> Malfunction_compiler.module_to_lambda
    |> Malfunction_compiler.lambda_to_cmx exec_name exec_name
    |> (fun t -> temps := Some t; t)
    |> Malfunction_compiler.link_executable exec_name
  with
  | 0 -> ()
  | _ -> delete_temps (); raise (HarnessFailed "Link error")
  | exception e ->
      Location.report_exception Format.str_formatter e;
      delete_temps ();
      raise (HarnessFailed (Format.flush_str_formatter ())) end;
  let (rd, wr) = Unix.open_process ("./" ^ exec_name) in
  cases
  |> List.map (function
    | `Bad_test _ | `Undefined _ -> Obj.repr 0
    | `Match (_, obj) | `NoMatch (_, obj) -> obj)
  |> List.iter (fun x -> Marshal.to_channel wr x []);
  flush wr;
  let answer = try input_line rd with End_of_file -> "" in
  let result = Unix.close_process (rd, wr) in
  delete_temps ();
  match result with
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

let run_file filename =
  let lexbuf = Lexing.from_channel (open_in filename) in
  Lexing.(lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = filename});
  let rec read_testcases acc =
    let open Malfunction_sexp in
    match read_next_sexp lexbuf with
    | loc, List [_, Atom "test"; test; exp] ->
       read_testcases ((`Test, loc,
                        Malfunction_parser.parse_expression test,
                        Malfunction_parser.parse_expression exp) :: acc)
    | loc, List [_, Atom "test-differ"; test; exp] ->
       read_testcases ((`TestDiffer, loc,
                        Malfunction_parser.parse_expression test,
                        Malfunction_parser.parse_expression exp) :: acc)
    | loc, List [_, Atom "test-undefined"; test] ->
       read_testcases ((`TestUndef, loc,
                        Malfunction_parser.parse_expression test,
                        Malfunction_parser.parse_expression (loc, Int 0)) :: acc)
    | loc, _ -> raise (Malfunction.SyntaxError (loc, "Bad test"))
    | exception End_of_file -> List.rev acc in
  Format.printf "%s: %!" filename;
  match Malfunction.with_error_reporting (Format.std_formatter) None
    (fun () -> Some (read_testcases []))
  with
  | None -> ()
  | Some cases ->
     let results = cases
     |> List.map (fun (ty, loc, test, expect) ->
       match eval expect with
       | exception (Error s) -> `Bad_test s
       | expectRes -> match eval test, reify expectRes with
         | exception (Error s) -> `Undefined s
         | exception (ReifyFailure s) -> `Bad_test s
         | testRes, expectObj when testRes <> expectRes -> `NoMatch (test, expectObj)
         | testRes, expectObj -> `Match (test, expectObj))
     |> run_tests in
     Format.printf "\n";
     let describe (ty, ({Lexing.pos_lnum = line}, _), _, _) result =
       let say fmt =
         Format.printf "%s:%d: " filename line;
         let endline ppf =
           Format.fprintf ppf "\n%!" in
         Format.kfprintf endline Format.std_formatter fmt in
       begin match ty, result with
       | _, `Bad_test s -> say "bad test: %s" s
       | _, `Crash s -> say "crash: %s" s
       | _, `Inconsistent -> say "inconsistent results"
       | `Test, `Match
       | `TestUndef, `Undefined _
       | `TestDiffer, `Different -> say "ok"
       | (`Test|`TestDiffer), `Undefined s -> say "undefined behaviour: %s" s
       | (`Test|`TestUndef), `Different -> say "values don't match"
       | (`TestDiffer|`TestUndef), `Match -> say "values match when not expected to" end;
       Format.printf "%!"
     in

     List.iter2 describe cases results

let () =
  match Sys.argv with
  | [| me |] -> Format.printf "Usage: %s <test files>\n" me
  | _ ->
     for i = 1 to Array.length Sys.argv - 1 do
       run_file (Sys.argv.(i))
     done
