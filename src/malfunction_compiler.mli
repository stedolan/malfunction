
type outfiles = {
  objfile : string;
  cmxfile : string;
  cmifile : string option
}
val delete_temps : outfiles -> unit 

type options = [`Verbose | `Shared] list

val compile_cmx : ?options:options -> string -> outfiles

type lambda_mod = int * Lambda.lambda

val module_to_lambda : ?options:options -> module_name:string -> module_id:Ident.t -> Malfunction_parser.moduleexp -> lambda_mod
val lambda_to_cmx : 
  ?options:options ->
  filename:string -> (* the filename being compiled (used to print warnings) *)
  prefixname:string -> (* the prefix for the output filenames *)
  module_name:string ->
  module_id:Ident.t ->
  lambda_mod -> outfiles
val link_executable : string -> outfiles -> int

val compile_and_load : ?options:options -> Malfunction.t -> Obj.t
