
type outfiles = {
  objfile : string;
  cmxfile : string
}
 

val compile_cmx : string -> outfiles




type lambda_mod = int * Lambda.lambda

val module_to_lambda : Malfunction_parser.moduleexp -> lambda_mod
val lambda_to_cmx : 
  string -> (* the filename being compiled (used to print warnings) *)
  string -> (* the prefix for the output filenames *)
  lambda_mod -> outfiles
