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


let lswitch (scr : lambda) (swi : lambda_switch) =
#if OCAML_VERSION >= (4, 06, 0)
  Lswitch(scr, swi, Location.none)
#else
  Lswitch(scr, swi)
#endif

let lfunction params body =
#if OCAML_VERSION >= (4, 08, 0)
  let params = List.map (fun x -> x, Pgenval) params in
#endif
  Lfunction {
     kind = Curried;
     params;
     body;
     loc = Location.none;
     attr = {
       inline = Default_inline;
       specialise = Default_specialise;
       is_a_functor = false;
#if OCAML_VERSION >= (4, 05, 0)
       stub = false;
#endif
#if OCAML_VERSION >= (4, 08, 0)
       local = Default_local;
#endif
     };
#if OCAML_VERSION >= (4, 08, 0)
     return = Pgenval;
#endif
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
  let apply = 
#if OCAML_VERSION >= (4, 08, 0)
    Lambda.subst (fun _ _ e -> e)
#else
    Lambda.subst
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

