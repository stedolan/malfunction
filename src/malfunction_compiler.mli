
type outfiles = {
  objfile : string;
  cmxfile : string;
  cmifile : string option
}
val delete_temps : outfiles -> unit 

type options = [`Verbose | `Shared] list

val compile_cmx : ?options:options -> string -> outfiles

type lambda_mod = int * Lambda.lambda

val module_to_lambda : ?options:options -> Malfunction_parser.moduleexp -> lambda_mod
val lambda_to_cmx : 
  ?options:options ->
  string -> (* the filename being compiled (used to print warnings) *)
  string -> (* the prefix for the output filenames *)
  lambda_mod -> outfiles
val link_executable : string -> outfiles -> int

val compile_and_load : ?options:options -> Malfunction.t -> Obj.t
