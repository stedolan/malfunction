open Malfunction

let with_error_reporting f =
  try f () with
  | SyntaxError ((locstart, locend), msg) ->
     let open Lexing in
     if locstart.pos_lnum = locend.pos_lnum then
       Printf.fprintf stderr "%s:%d:%d-%d: %s\n%!"
         locstart.pos_fname locstart.pos_lnum (locstart.pos_cnum - locstart.pos_bol) (locend.pos_cnum - locend.pos_bol) msg
     else
       Printf.fprintf stderr "%s:%d:%d-%d:%d %s\n%!"
         locstart.pos_fname locstart.pos_lnum (locstart.pos_cnum - locstart.pos_bol) locend.pos_lnum (locend.pos_cnum - locend.pos_bol) msg;
     1
  | x ->
     Location.report_exception Format.std_formatter x;
    1

let usage () =
  Printf.fprintf stderr "usage: ?\n"; 2

let repl () =
  let lexbuf = Lexing.from_channel stdin in
  let rec loop () =
    Printf.printf "# %!";
    let _ = with_error_reporting (fun () ->
      Malfunction_parser.read_expression lexbuf
      |> Malfunction_interpreter.eval; 0) in
    loop () in
  loop ()

let run mode impl output =
  Findlib.init ();
  match mode, impl with
  | `Cmx, Some file ->
     with_error_reporting (fun () -> let _ = Malfunction_compiler.compile_cmx file in 0)
  | `Compile, Some file ->
     with_error_reporting (fun () ->
       let tmpfiles = Malfunction_compiler.compile_cmx file in
       let output = match output with
         | None -> Compenv.output_prefix file
         | Some out -> out in
       let res =
         Sys.command (Printf.sprintf "ocamlfind ocamlopt -package zarith zarith.cmxa '%s' -o '%s'" (* urgh *)
                        tmpfiles.Malfunction_compiler.cmxfile output) in
       Malfunction_compiler.delete_temps tmpfiles;
       res)
  | `Eval, Some file ->
     0
  | `Eval, None ->
     repl ()
  | `Fmt, impl ->
     let lexbuf = Lexing.from_channel (match impl with Some f -> open_in f | None -> stdin) in
     Malfunction_sexp.(read_only_sexp lexbuf |> print Format.std_formatter);
     0
  | _ -> usage ()


let rec parse_args args =
  let impl = ref None in
  let output = ref None in
  let rec parse_opts mode = function
    | "-o" :: o :: rest -> output := Some o; parse_opts mode rest
    | i :: rest ->
       (match !impl with None -> (impl := Some i; parse_opts mode rest) | _ -> usage ())
    | [] -> run mode !impl !output in
  match args with
  | "cmx" :: rest -> parse_opts `Cmx rest
  | "compile" :: rest -> parse_opts `Compile rest
  | "eval" :: rest -> parse_opts `Eval rest
  | "fmt" :: rest -> parse_opts `Fmt rest
  | _ -> usage ()

let _ = exit (parse_args (List.tl (Array.to_list Sys.argv)))
