open Lambda

module Stdlib =
#if OCAML_VERSION < (4, 07, 0)
  Pervasives
#else
  Stdlib
#endif

let stdlib_module_name =
#if OCAML_VERSION < (4,07,0)
  "Pervasives"
#else
  "Stdlib"
#endif

let fresh =
#if OCAML_VERSION < (4, 08, 0)
  Ident.create
#else
  Ident.create_local
#endif

let loc_none =
#if OCAML_VERSION < (4, 11, 0)
  Location.none
#else
  Debuginfo.Scoped_location.Loc_unknown
#endif

let lswitch (scr : lambda) (swi : lambda_switch) =
#if OCAML_VERSION >= (4, 06, 0)
  Lswitch(scr, swi, loc_none)
#else
  Lswitch(scr, swi)
#endif

let lfunction params body =
#if OCAML_VERSION >= (4, 08, 0)
  let params = List.map (fun x -> x, Pgenval) params in
#endif
  lfunction 
    ~kind:Curried
     ~params
     ~body
     ~loc:loc_none
     ~attr:{
       inline = Default_inline;
       specialise = Default_specialise;
       is_a_functor = false;
       tmc_candidate = false;
       poll = Default_poll;
       stub = false;
       local = Default_local;
     }
     ~return:Pgenval

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

let transl_value_path loc env path =
#if OCAML_VERSION >= (4, 08, 0)
  Lambda.transl_value_path loc env path
#elif OCAML_VERSION >= (4, 06, 0)
  Lambda.transl_value_path ~loc env path
#else
  ignore loc;
  Lambda.transl_path env path
#endif

let pintcomp_cne =
#if OCAML_VERSION >= (4, 07, 0)
  Pintcomp Cne
#else
  Pintcomp Cneq
#endif

let make_switch_loc f =
#if OCAML_VERSION >= (4, 06, 0)
  fun _loc -> f
#else
  f
#endif

let with_loc f =
#if OCAML_VERSION >= (4, 06, 0)
  f
#else
  fun _loc -> f
#endif

let cmp_to_float_comparison op = 
#if OCAML_VERSION < (4, 07, 0)
  match op with
  | `Lt -> Cle
  | `Gt -> Cgt
  | `Lte -> Cle
  | `Gte -> Cge
  | `Eq -> Ceq
#else
  match op with
  | `Lt -> CFlt
  | `Gt -> CFgt
  | `Lte -> CFle
  | `Gte -> CFge
  | `Eq -> CFeq
#endif

module Subst : sig
  type t
  val empty : t
  val add : Ident.t -> Lambda.lambda -> t -> t
  val apply : t -> Lambda.lambda -> Lambda.lambda
end = struct
#if OCAML_VERSION < (4,07,0)
  type t = Lambda.lambda Ident.tbl
  let empty = Ident.empty
  let add = Ident.add
  let apply = Lambda.subst_lambda
#else
  type t = Lambda.lambda Ident.Map.t
  let empty = Ident.Map.empty
  let add = Ident.Map.add
  let apply t x = 
#if OCAML_VERSION >= (4, 08, 0)
    Lambda.subst (fun _ _ e -> e) t x
#else
    Lambda.subst t x
#endif
#endif
end

let root_initialization =
#if OCAML_VERSION < (4, 05, 0)
  Initialization
#else
  Root_initialization
#endif

let with_source_provenance _filename f =
#if OCAML_VERSION < (4, 06, 0)
  f ~source_provenance:(Timings.File _filename)
#else
  f
#endif

let with_ppf_dump ppf f =
#if OCAML_VERSION >= (4, 08, 0)
  f ~ppf_dump:ppf
#else
  f ppf
#endif

let load_path_find name =
#if OCAML_VERSION >= (4, 08, 0)
  Load_path.find_uncap name
#else
  Misc.find_in_path_uncap !Config.load_path name
#endif

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
      with_source_provenance filename (with_ppf_dump ppf flambda_middle_end)
        ~prefixname
        ~backend
        ~size
        ~filename
        ~module_ident:module_id
        ~module_initializer:lam)
    |> with_ppf_dump ppf (
        with_source_provenance filename (Asmgen.compile_implementation_flambda ?toplevel:None)
        prefixname
        ~required_globals
        ~backend)
  end else begin
    (* FIXME: main_module_block_size is wrong *)
    code
    |> (fun code -> Lambda.{ module_ident = module_id; required_globals;
                             code; main_module_block_size = size })
    |> with_ppf_dump ppf
       (with_source_provenance filename (asmgen_compile_implementation_clambda ~backend)
         prefixname);
  end;
#else
  let program = Lambda.{code; main_module_block_size = size; module_ident = module_id; required_globals } in
  let middle_end =
    if Config.flambda then Flambda_middle_end.lambda_to_clambda
    else Closure_middle_end.lambda_to_clambda
  in
  let _ = filename in 
  Asmgen.compile_implementation
    ?toplevel:None 
    ~backend 
   (* ~filename *)
    ~prefixname 
    ~middle_end 
    ~ppf_dump:ppf
    program
#endif
