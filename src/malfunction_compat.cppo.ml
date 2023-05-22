open Lambda

let loc_none =
#if OCAML_VERSION < (4, 11, 0)
  Location.none
#else
  Debuginfo.Scoped_location.Loc_unknown
#endif

let lswitch (scr : lambda) (swi : lambda_switch) =
  Lswitch(scr, swi, loc_none)

let lfunction params body =
  let params = List.map (fun x -> x, Pgenval) params in
  let attr = {
    inline = Default_inline;
    specialise = Default_specialise;
    is_a_functor = false;
    stub = false;
    local = Default_local;
#if OCAML_VERSION >= (4, 14, 0)
    poll = Default_poll;
    tmc_candidate = false;
#endif
  } in
#if OCAML_VERSION >= (4, 14, 0)
  lfunction
    ~kind:Curried
    ~params
    ~return:Pgenval
    ~body
    ~attr
    ~loc:loc_none
#else
  Lfunction {
     kind = Curried;
     params;
     body;
     loc = loc_none;
     attr;
     return = Pgenval;
   }
#endif

let lapply fn args =
  Lapply {
    ap_func = fn;
    ap_args = args;
    ap_loc = loc_none; (* FIXME *)
#if OCAML_VERSION < (4, 12, 0)
    ap_should_be_tailcall = false;
#else
    ap_tailcall = Default_tailcall;
#endif
    ap_inlined = Default_inline;
    ap_specialised = Default_specialise
  }

module Subst : sig
  type t
  val empty : t
  val add : Ident.t -> Lambda.lambda -> t -> t
  val apply : t -> Lambda.lambda -> Lambda.lambda
end = struct
  type t = Lambda.lambda Ident.Map.t
  let empty = Ident.Map.empty
  let add = Ident.Map.add
  let apply t x = 
    Lambda.subst (fun _ _ e -> e) t x
end

let compmisc_init_path () =
#if OCAML_VERSION < (4, 09, 0)
  Compmisc.init_path true
#else
  Compmisc.init_path ()
#endif

let simplify_lambda lam =
#if OCAML_VERSION < (4, 09, 0)
  Simplif.simplify_lambda "malfunction" lam
#else
  Simplif.simplify_lambda lam
#endif

let flambda_middle_end =
#if OCAML_VERSION < (4, 09, 0)
  Middle_end.middle_end
#elif OCAML_VERSION < (4, 10, 0)
  Flambda_middle_end.middle_end
#else
  Flambda_middle_end.lambda_to_clambda
#endif

let asmgen_compile_implementation_clambda ~backend =
#if OCAML_VERSION < (4, 09, 0)
  ignore backend;
  Asmgen.compile_implementation_clambda ?toplevel:None
#elif OCAML_VERSION < (4, 10, 0)
  Asmgen.compile_implementation_clambda ?toplevel:None ~backend
#else
  Asmgen.compile_implementation ?toplevel:None ~backend
    ~middle_end:Closure_middle_end.lambda_to_clambda
#endif

let compile_implementation
  ~prefixname ~filename ~module_id ~backend ~required_globals ~ppf (size, code) =
#if OCAML_VERSION < (4,10,0)
  if Config.flambda then begin
    code
    |> (fun lam ->
      flambda_middle_end
        ~ppf_dump:ppf
        ~prefixname
        ~backend
        ~size
        ~filename
        ~module_ident:module_id
        ~module_initializer:lam)
    |> Asmgen.compile_implementation_flambda ?toplevel:None ~ppf_dump:ppf
        prefixname
        ~required_globals
        ~backend
  end else begin
    (* FIXME: main_module_block_size is wrong *)
    code
    |> (fun code -> Lambda.{ module_ident = module_id; required_globals;
                             code; main_module_block_size = size })
    |> (asmgen_compile_implementation_clambda ~backend ~ppf_dump:ppf
         prefixname);
  end;
#else
  let program = Lambda.{code; main_module_block_size = size; module_ident = module_id; required_globals } in
  let middle_end =
    if Config.flambda then Flambda_middle_end.lambda_to_clambda
    else Closure_middle_end.lambda_to_clambda
  in
#if OCAML_VERSION >= (4, 13, 0)
  ignore filename;
  Asmgen.compile_implementation
    ?toplevel:None ~backend ~prefixname ~middle_end ~ppf_dump:ppf
    program
#else
  Asmgen.compile_implementation
    ?toplevel:None ~backend ~filename ~prefixname ~middle_end ~ppf_dump:ppf
    program
#endif
#endif
