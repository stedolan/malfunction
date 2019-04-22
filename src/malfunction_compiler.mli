
type outfiles = {
  objfile : string;
  cmxfile : string;
  cmifile : string option
}
val delete_temps : outfiles -> unit 

type options = [`Verbose | `Shared] list

val compile_module :
  ?options:options ->
  filename:string ->
  Malfunction_parser.moduleexp ->
  outfiles

val compile_cmx : ?options:options -> string -> outfiles

val link_executable : string -> outfiles -> int

val compile_and_load : ?options:options -> Malfunction.t -> Obj.t
