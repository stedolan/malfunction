
type outfiles = {
  objfile : string;
  cmxfile : string;
  cmifile : string option
}
val delete_temps : outfiles -> unit 

type options = [`Verbose | `Shared | `ForPack of string | `Package of string | `Dontlink of string | `Linkpkg | `Thread | `Optimize] list

val compile_module :
  ?options:options ->
  filename:string ->
  Malfunction_parser.moduleexp ->
  outfiles

val compile_cmx : ?options:options -> string -> outfiles

val link_executable : ?options:options -> string -> outfiles -> int

val compile_and_load : ?options:options -> Malfunction.t -> Obj.t
