open Lambda
open Asttypes

open Malfunction_parser

module IntSwitch = struct

  (* Convert a list of possibly-overlapping intervals to a list of disjoint intervals *)

  type action = int (* lower numbers more important *)

  (* cases is a sorted list
     cases that begin lower appear first
     when two cases begin together, more important appears first *)

  type case = int * int * action (* start position, end position, priority *)
  type cases = case list (* sorted by start position then priority *)

  (* the inactive list is a list of (endpoint, priority) pairs representing
     intervals that we are currently inside, but are overridden by a more important one.
     subsequent elements of the list have strictly higher priorities and strictly later endpoints *)
  type inactive = (int * action) list

  let rec insert_inactive max act = function
    | [] -> [(max, act)]
    | (max', act') as i' :: rest when act' < act ->
       (* this interval should appear before the new one *)
       i' ::
         (if max' <= max then
             (* new interval will never be active *)
             rest
          else
             insert_inactive max act rest)

    | (max', act') :: rest when max' <= max ->
       assert (act < act');
       (* this interval will is contained by the new one, so never becomes active *)
       insert_inactive max act rest

    | ov ->
       (* new interval both more important and ends sooner, so prepend *)
       (max, act) :: ov

  type state =
    | Hole (* not currently in any interval *)
    | Interval of (* in an interval... *)
      int (* since this position *)
      * int (* until here *)
      * action (* with this action *)
      * inactive (* overriding these inactive intervals *)

  let state_suc = function
    | Hole -> failwith "state_suc of Hole undefined"
    | Interval (_, _, _, []) -> Hole
    | Interval (_, s_max, _, (max', act') :: rest) ->
       assert (s_max < max');
       (* can compute s_max + 1 without overflow, because inactive interval ends later *)
       Interval (s_max + 1, max', act', rest)

  type result = case list (* may have duplicate actions, disjoint, sorted by position *)
  let rec to_disjoint_intervals c_state c_cases : case list =
    match c_state, c_cases with
    | Hole, [] -> []

    | Hole, ((min, max, act) :: cases) ->
       to_disjoint_intervals (Interval (min, max, act, [])) cases

    | Interval (entered, max, act, _) as state, [] ->
       (entered, max, act) :: to_disjoint_intervals (state_suc state) []

    | Interval (s_entered, s_max, s_act, _) as state,
      (((min, max, act) :: _) as cases) when s_max < min ->
       (* active interval ends before this case begins *)
       (s_entered, s_max, s_act) :: to_disjoint_intervals (state_suc state) cases

    (* below here, we can assume min <= i.s_max: active interval overlaps current case *)
    | Interval (s_entered, s_max, s_act, s_inactive), ((min, max, act) :: cases) when s_act < act ->
       (* no change to active interval, but this case may become an inactive one *)
       to_disjoint_intervals (Interval (s_entered, s_max, s_act, insert_inactive max act s_inactive)) cases

    | Interval (s_entered, s_max, s_act, s_inactive), ((min, max, act) :: cases) ->
       (* new active interval, so old one becomes inactive *)
       assert (s_entered <= min); assert (min <= s_max); assert (act < s_act);
       let r =
         if s_entered = min then
           (* old interval was not active long enough to produce output *)
           []
         else
           [(s_entered, min - 1, s_act)] in
       r @ to_disjoint_intervals
         (Interval (min, max, act, insert_inactive s_max s_act s_inactive)) cases


  (* unfortunately, this is not exposed from matching.ml, so copy-paste *)
  module Switcher = Switch.Make (struct
    type primitive = Lambda.primitive

    let eqint = Pintcomp Ceq
    let neint = Pintcomp Cneq
    let leint = Pintcomp Cle
    let ltint = Pintcomp Clt
    let geint = Pintcomp Cge
    let gtint = Pintcomp Cgt

    type act = Lambda.lambda

    let make_prim p args = Lprim (p,args)
    let make_offset arg n = match n with
    | 0 -> arg
    | _ -> Lprim (Poffsetint n,[arg])

    let bind arg body =
      let newvar,newarg = match arg with
      | Lvar v -> v,arg
      | _      ->
          let newvar = Ident.create "switcher" in
          newvar,Lvar newvar in
      bind Alias newvar arg (body newarg)
    let make_const i = Lconst (Const_base (Const_int i))
    let make_isout h arg = Lprim (Pisout, [h ; arg])
    let make_isin h arg = Lprim (Pnot,[make_isout h arg])
    let make_if cond ifso ifnot = Lifthenelse (cond, ifso, ifnot)
    let make_switch arg cases acts =
      let l = ref [] in
      for i = Array.length cases-1 downto 0 do
        l := (i,acts.(cases.(i))) ::  !l
      done ;
      Lswitch(arg,
              {sw_numconsts = Array.length cases ; sw_consts = !l ;
               sw_numblocks = 0 ; sw_blocks =  []  ;
               sw_failaction = None})
    let make_catch d =
      match d with
      | Lstaticraise (i, []) -> i, (fun e -> e)
      | _ ->
         let i = next_raise_count () in
         i, fun e -> Lstaticcatch(e, (i, []), d)
    let make_exit i = Lstaticraise (i,[])
  end)

  let compile_int_switch scr overlapped_cases =
    assert (overlapped_cases <> []);
    let actions = Array.of_list (overlapped_cases |> List.map snd) in
    let cases = overlapped_cases
      |> List.mapi (fun idx (`Intrange (min, max), act) -> (min, max, idx))
      |> List.stable_sort (fun (min, max, idx) (min', max', idx') -> compare min min')
      |> to_disjoint_intervals Hole in
    let occurrences = Array.make (Array.length actions) 0 in
    let rec count_occurrences = function
      | [] -> assert false
      | [(min, max, act)] ->
         occurrences.(act) <- occurrences.(act) + 1
      | (min, max, act) :: (((min', max', act') :: _) as rest) ->
         occurrences.(act) <- occurrences.(act) + 1;
         begin if max + 1 <> min' then
           (* When the interval list contains a hole, jump tables generated by
              switch.ml may contain spurious references to action 0.
              See PR#6805 *)
           occurrences.(0) <- occurrences.(0) + 1
         end;
         count_occurrences rest in
    count_occurrences cases;
    let open Switch in
    let store : Lambda.lambda t_store =
      { act_get = (fun () ->
          Array.copy actions);
        act_get_shared = (fun () ->
          actions |> Array.mapi (fun i act ->
            if occurrences.(i) > 1 then Shared act else Single act));
        act_store = (fun _ -> failwith "store unimplemented");
        act_store_shared = (fun _ -> failwith "store_shared unimplemented") } in
    let cases = Array.of_list cases in
    let (low, _, _) = cases.(0) and (_, high, _) = cases.(Array.length cases - 1) in
    Switcher.zyva (low, high) scr cases store
end

let lookup env v =
  let open Types in
  let open Primitive in
  let (path, descr) = Env.lookup_value (* ~loc:(parse_loc loc) *) v env in
  match descr.val_kind with
  | Val_reg -> `Val (Lambda.transl_path (* ~loc:(parse_loc loc) *) env path)
  | Val_prim(p) -> 
     if p.prim_name.[0] = '%' then failwith ("unimplemented primitive " ^ p.prim_name);
     `Prim p
  | _ -> failwith "unexpected kind of value"


let builtin env path args =
  let p = match path with
    | path1 :: pathrest ->
       List.fold_left (fun id s -> Longident.Ldot (id, s))
         (Longident.Lident path1) pathrest
    | _ -> assert false in
  match lookup env p with
  | `Val v ->
     Lapply {
       ap_func = v;
       ap_args = args;
       ap_loc = Location.none; (* FIXME *)
       ap_should_be_tailcall = false;
       ap_inlined = Default_inline;
       ap_specialised = Default_specialise
     }
  | `Prim p ->
     Lprim (Pccall p, args)

let rec to_lambda env = function
  | Mvar v ->
     Lvar v
  | Mlambda (params, e) ->
     Lfunction {
       kind = Curried;
       params;
       body = to_lambda env e;
       attr = {
         inline = Default_inline;
         specialise = Default_specialise;
         is_a_functor = false
       }
     }
  | Mapply (fn, args) ->
     let ap_func fn =
       Lapply {
         ap_func = fn;
         ap_args = List.map (to_lambda env) args;
         ap_loc = Location.none; (* FIXME *)
         ap_should_be_tailcall = false;
         ap_inlined = Default_inline;
         ap_specialised = Default_specialise;
       } in
     (match fn with
     | Mglobal v ->
        (match lookup env v with
        | `Val v -> ap_func v
        | `Prim p ->
           Lprim (Pccall p, List.map (to_lambda env) args))
     | fn ->
        ap_func (to_lambda env fn))
  | Mlet (bindings, body) ->
     bindings_to_lambda env bindings (to_lambda env body)
  | Mint (`Int n) ->
     Lconst (Const_base (Const_int n))
  | Mint (`Int32 n) ->
     Lconst (Const_base (Const_int32 n))
  | Mint (`Int64 n) ->
     Lconst (Const_base (Const_int64 n))
  | Mint (`Bigint n) ->
     (match Z.to_int n with
     | n' ->
        assert (Obj.repr n = Obj.repr n');
        Lconst (Const_base (Const_int n'))
     | exception Z.Overflow ->
        builtin env ["Z"; "of_string"] [Lconst (Const_immstring (Z.to_string n))])
  | Mstring s ->
     Lconst (Const_immstring s)
  | Mglobal v ->
     (match lookup env v with
     | `Val v -> v
     | `Prim p -> failwith ("primitive " ^ Primitive.native_name p ^ " found where value expected"))
  | Mswitch (scr, cases) ->
     let scr = to_lambda env scr in
     let rec flatten acc = function
       | ([], _) :: _ -> assert false
       | ([sel], e) :: rest -> flatten ((sel, to_lambda env e) :: acc) rest
       | (sels, e) :: rest ->
          let i = next_raise_count () in
          let cases = List.map (fun s -> s, Lstaticraise(i, [])) sels in
          Lstaticcatch (flatten (cases @ acc) rest, (i, []), to_lambda env e)
       | [] ->
          let rec partition (ints, tags, deftag) = function
            | [] -> (List.rev ints, List.rev tags, deftag)
            | (`Tag _, _) as c :: cases -> partition (ints, c :: tags, deftag) cases
            | (`Deftag, _) as c :: cases -> partition (ints, tags, Some c) cases
            | (`Intrange _, _) as c :: cases -> partition (c :: ints, tags, deftag) cases in
          let (intcases, tagcases, deftag) = partition ([],[],None) (List.rev acc) in
          let id = Ident.create "switch" in
          Llet (Strict, id, scr,
            let scr = Lvar id in
            let tagswitch = match tagcases, deftag with
              | [], None -> None
              | [_,e], None | [], Some (_, e) -> Some e
              | tags, def ->
                 let numtags = match def with
                   | Some e -> (max_tag :> int)
                   | None -> 1 + List.fold_left (fun s (`Tag i, e) -> max s (i :> int)) (-1) tags in
                 Some (Lswitch (scr, {
                   sw_numconsts = 0; sw_consts = []; sw_numblocks = numtags;
                   sw_blocks = List.map (fun (`Tag i, e) -> i, e) tags;
                   sw_failaction = match def with None -> None | Some (`Deftag,e) -> Some e
                 })) in
            let intswitch = match intcases with
              | [] -> None
              | [_,e] -> Some e
              | ints -> Some (IntSwitch.compile_int_switch scr ints) in
            match intswitch, tagswitch with
            | None, None -> assert false
            | None, Some e | Some e, None -> e
            | Some eint, Some etag ->
               Lifthenelse (Lprim (Pisint, [scr]), eint, etag)) in
     (match cases with
     | [[`Intrange (0, 0)], ezero; _, enonzero]
     | [_, enonzero; [`Intrange (0, 0)], ezero] ->
        (* special case comparisons with zero *)
        Lifthenelse(scr, to_lambda env enonzero, to_lambda env ezero)
     | cases -> flatten [] cases)
  | Mintop1 (op, ty, e) ->
     let e = to_lambda env e in
     let ones32 = Const_base (Asttypes.Const_int32 (Int32.of_int (-1))) in
     let ones64 = Const_base (Asttypes.Const_int64 (Int64.of_int (-1))) in
     let code = match op, ty with
       | `Neg, `Int -> Lprim (Pnegint, [e])
       | `Neg, `Int32 -> Lprim (Pnegbint Pint32, [e])
       | `Neg, `Int64 -> Lprim (Pnegbint Pint64, [e])
       | `Neg, `Bigint -> builtin env ["Z"; "neg"] [e]
       | `Not, `Int -> Lprim (Pnot, [e])
       | `Not, `Int32 ->
          Lprim (Pxorbint Pint32, [e; Lconst ones32])
       | `Not, `Int64 ->
          Lprim (Pxorbint Pint64, [e; Lconst ones64])
       | `Not, `Bigint -> builtin env ["Z"; "lognot"] [e] in
     code
  | Mintop2 (op, ((`Int|`Int32|`Int64) as ty), e1, e2) ->
     let e1 = to_lambda env e1 in
     let e2 = to_lambda env e2 in
     let prim = match ty with
       | `Int ->
          (match op with
            `Add -> Paddint | `Sub -> Psubint
          | `Mul -> Pmulint | `Div -> Pdivint | `Mod -> Pmodint
          | `And -> Pandint | `Or -> Porint | `Xor -> Pxorint
          | `Lsl -> Plslint | `Lsr -> Plsrint | `Asr -> Pasrint
          | `Lt -> Pintcomp Clt | `Gt -> Pintcomp Cgt
          | `Lte -> Pintcomp Cle | `Gte -> Pintcomp Cge
          | `Eq -> Pintcomp Ceq)
       | (`Int32 | `Int64) as ty ->
          let t = match ty with `Int32 -> Pint32  | `Int64 -> Pint64 in
          (match op with
            `Add -> Paddbint t | `Sub -> Psubbint t
          | `Mul -> Pmulbint t | `Div -> Pdivbint t | `Mod -> Pmodbint t
          | `And -> Pandbint t | `Or -> Porbint t | `Xor -> Pxorbint t
          | `Lsl -> Plslbint t | `Lsr -> Plsrbint t | `Asr -> Pasrbint t
          | `Lt -> Pbintcomp (t, Clt) | `Gt -> Pbintcomp (t, Cgt)
          | `Lte -> Pbintcomp (t, Cle) | `Gte -> Pbintcomp (t, Cge)
          | `Eq -> Pbintcomp (t, Ceq)) in
     Lprim (prim, [e1; e2])
  | Mintop2 (op, `Bigint, e1, e2) ->
     let e1 = to_lambda env e1 in
     let e2 = to_lambda env e2 in
     let fn = match op with
       | `Add -> "add" | `Sub -> "sub"
       | `Mul -> "mul" | `Div -> "div" | `Mod -> "rem"
       | `And -> "logand" | `Or -> "logor" | `Xor -> "logxor"
       | `Lsl -> "shift_left" | `Lsr -> "shift_right" | `Asr -> "shift_right"
       | `Lt -> "lt" | `Gt -> "gt"
       | `Lte -> "leq" | `Gte -> "geq" | `Eq -> "equal" in
     builtin env ["Z"; fn] [e1; e2]
  | Mseqget (ty, seq, idx) ->
     let prim = match ty with
       | `Array -> Parrayrefs Paddrarray
       | `Bytevec -> Pstringrefs
(*       | `Floatvec -> Parrayrefs Pfloatarray *) in
     Lprim (prim, [to_lambda env seq; to_lambda env idx])
  | Mseqset (ty, seq, idx, v) ->
     let prim = match ty with
       | `Array -> Parraysets Paddrarray
       | `Bytevec -> Pstringsets
(*       | `Floatvec -> Parraysets Pfloatarray *) in
     Lprim (prim, [to_lambda env seq; to_lambda env idx; to_lambda env v])
  | Mseqlen (ty, seq) ->
     let prim = match ty with
       | `Array -> Parraylength Paddrarray
       | `Bytevec -> Pstringlength
(*       | `Floatvec -> Parraylength Pfloatarray *) in
     Lprim (prim, [to_lambda env seq])
  | Mblock (tag, vals) ->
     Lprim (Pmakeblock(tag, Immutable), List.map (to_lambda env) vals)
  | Mfield (idx, e) ->
     Lprim (Pfield(idx), [to_lambda env e])

and bindings_to_lambda env bindings body =
  List.fold_right (fun b rest -> match b with
  | `Unnamed e ->
     Lsequence (to_lambda env e, rest)
  | `Named (n, e) ->
     Llet (Strict, n, to_lambda env e, rest)
  | `Recursive bs ->
     Lletrec (List.map (fun (n, e) -> (n, to_lambda env e)) bs, rest))
    bindings body


let setup_options () =
  Clflags.native_code := true;
  Clflags.flambda_invariant_checks := true;
  Clflags.nopervasives := true;
  Clflags.dump_lambda := true;
  Clflags.dump_cmm := true;
  Clflags.keep_asm_file := true;
  Clflags.include_dirs := [Findlib.package_directory "zarith"];
  Clflags.inlining_report := true;

  Compenv.(readenv Format.std_formatter (Before_compile "malfunction"));
  Compmisc.init_path true


let module_to_lambda (Mmod (bindings, exports)) =
  setup_options ();
  let print_if flag printer arg =
    if !flag then Format.printf "%a@." printer arg;
    arg in

  let env = Compmisc.initial_env () in
  let code = 
    bindings_to_lambda env bindings
      (Lprim (Pmakeblock(0, Immutable), List.map (to_lambda env) exports)) in

  let lambda = code
  |> print_if Clflags.dump_rawlambda Printlambda.lambda
  |> Simplif.simplify_lambda
  |> print_if Clflags.dump_lambda Printlambda.lambda in

  (List.length exports, lambda)



let backend = (module struct
  include Compilenv
  include Import_approx
  include Arch
  let max_sensible_number_of_arguments =
    Proc.max_arguments_for_tailcalls - 1
end : Backend_intf.S)

type outfiles = {
  objfile : string;
  cmxfile : string
}


type lambda_mod = int * Lambda.lambda

let delete_temps { objfile; cmxfile } =
  Misc.remove_file objfile;
  Misc.remove_file cmxfile

let lambda_to_cmx filename prefixname (size, code) =
  let ppf = Format.std_formatter in
  let outfiles = {
    cmxfile = prefixname ^ ".cmx";
    objfile = prefixname ^ Config.ext_obj
  } in
  setup_options ();
  try
    let source_provenance = Timings.File filename in
    let modulename = Compenv.module_of_filename ppf filename prefixname in
    let module_ident = Ident.create_persistent modulename in
    let cmi = modulename ^ ".cmi" in
    Env.set_unit_name modulename;
    Compilenv.reset ~source_provenance ?packname:!Clflags.for_package modulename;
    ignore (match Misc.find_in_path_uncap !Config.load_path cmi with
        | file -> Env.read_signature modulename file
        | exception Not_found ->
           Typemod.(raise(Error(Location.in_file filename,
                                Env.empty,
                                Interface_not_compiled cmi))));
    code
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
        ~source_provenance
        prefixname
        ~backend
        ppf;
    Compilenv.save_unit_info outfiles.cmxfile;
    Warnings.check_fatal ();
    outfiles
  with e ->
    delete_temps outfiles;
    raise e
        

let compile_cmx filename =
  let prefixname = Compenv.output_prefix filename in
  let lexbuf = Lexing.from_channel (open_in filename) in
  Lexing.(lexbuf.lex_curr_p <-
            { lexbuf.lex_curr_p with pos_fname = filename });
  Malfunction_parser.read_module lexbuf
  |> module_to_lambda
  |> lambda_to_cmx filename prefixname
