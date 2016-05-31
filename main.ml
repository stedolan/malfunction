(*

filename: source file name. Used for error messages and debug info (?)
debug info superseded by real location data.

ok, filename is where we get the sexps from.


prefixname is the basename of all output files.


*)
let compile ppf filename =
  Clflags.native_code := true;
  Clflags.flambda_invariant_checks := true;
  Clflags.nopervasives := true;
  Clflags.dump_lambda := true;
  Clflags.keep_asm_file := true;
  Compenv.(readenv ppf (Before_compile filename));

  let prefixname = Compenv.output_prefix filename in

  let backend = (module struct
    let symbol_for_global' = Compilenv.symbol_for_global'
    let closure_symbol = Compilenv.closure_symbol
      
    let really_import_approx = Import_approx.really_import_approx
    let import_symbol = Import_approx.import_symbol

    let size_int = Arch.size_int
    let big_endian = Arch.big_endian
      
    let max_sensible_number_of_arguments =
    (* The "-1" is to allow for a potential closure environment parameter. *)
      Proc.max_arguments_for_tailcalls - 1
  end : Backend_intf.S) in


  if !Clflags.classic_inlining then begin
    Clflags.default_simplify_rounds := 1;
    Clflags.use_inlining_arguments_set Clflags.classic_arguments;
    Clflags.unbox_free_vars_of_closures := false;
    Clflags.unbox_specialised_args := false
  end;

  Clflags.inlining_report := true;



  let source_provenance = Timings.File filename in

  Compmisc.init_path true;
  let modulename = Compenv.module_of_filename ppf filename prefixname in
  let module_ident = Ident.create_persistent modulename in
  Env.set_unit_name modulename;
  Compilenv.reset ~source_provenance ?packname:!Clflags.for_package modulename;

  let init_env = Compmisc.initial_env () in

  let cmxfile = prefixname ^ ".cmx" in
  let objfile = prefixname ^ Config.ext_obj in

  let print_if flag printer arg =
    if !flag then Format.fprintf ppf "%a@." printer arg;
    arg in

  let check_cmi () =
    let sourceintf =
      Misc.chop_extension_if_any filename ^ !Config.interface_suffix in
    if Sys.file_exists sourceintf then begin
      let dclsig = match Misc.find_in_path_uncap !Config.load_path (modulename ^ ".cmi") with
        | file -> Env.read_signature modulename file
        | exception Not_found ->
           Typemod.(raise(Error(Location.in_file filename, Env.empty,
                                Interface_not_compiled sourceintf))) in
      ()
    end else begin
      failwith "no .mli found"
    end in

  let comp chan =
    let (size, lambda) = chan
      |> Lexing.from_channel
      |> Sexp.read_sexp
      |> (fun s -> Format.printf "%a\n%!" Sexp.print_sexp s; s)
      |> Malfunction.parse_mod init_env in
    check_cmi ();
    lambda
    |> print_if Clflags.dump_rawlambda Printlambda.lambda
    |> Simplif.simplify_lambda
    |> print_if Clflags.dump_lambda Printlambda.lambda
    |> (fun lam ->
      Middle_end.middle_end ppf
        ~source_provenance
        ~prefixname
        ~size
        ~filename
        ~module_ident
        ~backend
        ~module_initializer:lam)
    |> Asmgen.compile_implementation_flambda 
        ~source_provenance prefixname ~backend ppf;
  in
  try 
    Timings.time (Timings.Generate filename) comp (open_in filename);
    Compilenv.save_unit_info cmxfile;
    Warnings.check_fatal ();
  with x ->
    Misc.remove_file objfile;
    Misc.remove_file cmxfile;
    raise x


let () =
  Compmisc.init_path true;
  try
    compile Format.std_formatter (Sys.argv.(1))
  with 
    Sexp.SyntaxError ((locstart, locend), msg) ->
      let open Lexing in
      if locstart.pos_lnum = locend.pos_lnum then
        Printf.fprintf stderr "%s:%d:%d-%d: %s\n%!" 
          locstart.pos_fname locstart.pos_lnum (locstart.pos_cnum - locstart.pos_bol) (locend.pos_cnum - locend.pos_bol) msg
      else
        Printf.fprintf stderr "%s:%d:%d-%d:%d %s\n%!" 
          locstart.pos_fname locstart.pos_lnum (locstart.pos_cnum - locstart.pos_bol) locend.pos_lnum (locend.pos_cnum - locend.pos_bol) msg;
      exit 2
    | x ->
      Location.report_exception Format.std_formatter x;
      exit 2
