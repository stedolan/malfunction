open Malfunction
(*

filename: source file name. Used for error messages and debug info (?)
debug info superseded by real location data.

ok, filename is where we get the sexps from.


prefixname is the basename of all output files.


*)

let with_error_reporting f =
  try f (); 0 with
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

let run mode impl output =
  Findlib.init ();
  match mode, impl with
  | `Cmx, Some file ->
     with_error_reporting (fun () -> Malfunction_compiler.compile_cmx file)
  | `Eval, Some file ->
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
  | "compile" :: rest -> parse_opts `Cmx rest
  | "eval" :: rest -> parse_opts `Eval rest
  | _ -> usage ()

let _ = exit (parse_args (List.tl (Array.to_list Sys.argv)))
