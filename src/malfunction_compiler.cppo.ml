open Lambda
open Asttypes

open Malfunction
open Malfunction_parser

(* List.map, but guarantees left-to-right evaluation *)
let rec lrmap f = function
| [] -> []
| (x :: xs) -> let r = f x in r :: lrmap f xs

(* Enforce left-to-right evaluation order by introducing 'let' bindings *)

let rec reorder = function
| Mvar _
| Mlambda _
| Mint _
| Mstring _
| Mglobal _ as t -> `Pure, t

| Mapply (f, xs) ->
   reorder_sub `Impure (fun ev ->
     let f = ev f in
     let xs = lrmap ev xs in
     Mapply (f, xs))

| Mlet (bindings, body) ->
   let bindings = reorder_bindings bindings in
   let _, body = reorder body in
   `Impure, Mlet (bindings, body)

| Mswitch (e, cases) ->
   `Impure, Mswitch (snd (reorder e), List.map (fun (c, e) -> c, snd (reorder e)) cases)

| Mintop1(op, ty, t) ->
   reorder_sub `Pure (fun ev ->
     Mintop1(op, ty, ev t))

| Mintop2(op, ty, t1, t2) ->
   reorder_sub `Pure (fun ev ->
     let t1 = ev t1 in
     let t2 = ev t2 in
     Mintop2(op, ty, t1, t2))

| Mconvert(src, dst, t) -> 
   reorder_sub `Pure (fun ev ->
     Mconvert(src, dst, ev t))

| Mvecnew(ty, len, def) ->
   reorder_sub `Pure (fun ev ->
     let len = ev len in
     let def = ev def in
     Mvecnew(ty, len, def))

| Mvecget(ty, vec, idx) ->
   reorder_sub `Impure (fun ev ->
     let vec = ev vec in
     let idx = ev idx in
     Mvecget(ty, vec, idx))

| Mvecset(ty, vec, idx, v) ->
   reorder_sub `Impure (fun ev ->
     let vec = ev vec in
     let idx = ev idx in
     let v = ev v in
     Mvecset(ty, vec, idx, v))

| Mveclen(ty, vec) ->
   reorder_sub `Pure (fun ev ->
     let vec = ev vec in
     Mveclen(ty, vec))

| Mblock (n, ts) ->
   reorder_sub `Pure (fun ev ->
     Mblock(n, lrmap ev ts))

| Mfield (n, t) ->
   reorder_sub `Impure (fun ev ->
     Mfield (n, ev t))

and reorder_bindings bindings =
  bindings
  |> lrmap (function
    | `Unnamed t -> `Unnamed (snd (reorder t))
    | `Named (v, t) -> `Named (v, snd (reorder t))
    | `Recursive _ as ts -> ts (* must be functions *))

and reorder_sub p f =
  let bindings = ref [] in
  let r = f (fun e ->
    match reorder e with
    | `Pure, e -> e
    | `Impure, e ->
       let id = Ident.create "tmp" in
       bindings := (`Named (id, e)) :: !bindings;
       Mvar id) in
  match List.rev !bindings with
  | [] -> p, r
  | bindings -> `Impure, (Mlet (bindings, r))


let lprim p args =
#if OCAML_VERSION = (4, 03, 0)
  Lprim (p, args)
#else
  Lprim (p, args, Location.none)
#endif

let llet id exp body =
#if OCAML_VERSION = (4, 03, 0)
  Llet (Strict, id, exp, body)
#else
  Llet (Strict, Pgenval, id, exp, body)
#endif

let pmakeblock tag mut =
#if OCAML_VERSION = (4, 03, 0)
  Pmakeblock (tag, mut)
#else
  Pmakeblock (tag, mut, None)
#endif

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

    let make_prim p args = lprim p args
    let make_offset arg n = match n with
    | 0 -> arg
    | _ -> lprim (Poffsetint n) [arg]

    let bind arg body =
      let newvar,newarg = match arg with
      | Lvar v -> v,arg
      | _      ->
          let newvar = Ident.create "switcher" in
          newvar,Lvar newvar in
      bind Alias newvar arg (body newarg)
    let make_const i = Lconst (Const_base (Const_int i))
    let make_isout h arg = lprim Pisout [h ; arg]
    let make_isin h arg = lprim Pnot [make_isout h arg]
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
  let (path, descr) = try
      Env.lookup_value (* ~loc:(parse_loc loc) *) v env
    with
      Not_found -> failwith ("global not found: " ^ String.concat "." (Longident.flatten v)) in
  match descr.val_kind with
  | Val_reg -> `Val (Lambda.transl_path (* ~loc:(parse_loc loc) *) env path)
  | Val_prim(p) ->
     let p = match p.prim_name with
       | "%equal" ->
          Primitive.simple ~name:"caml_equal" ~arity:2 ~alloc:true
       | "%compare" ->
          Primitive.simple ~name:"caml_compare" ~arity:2 ~alloc:true
       | s when s.[0] = '%' ->
          failwith ("unimplemented primitive " ^ p.prim_name);
       | _ ->
          p in
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
     lprim (Pccall p) args

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
#if OCAML_VERSION > (4, 04, 0)
         ; stub = false
#endif
       };
#if OCAML_VERSION > (4, 03, 0)
       loc = Location.none;
#endif
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
           lprim (Pccall p) (List.map (to_lambda env) args))
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
          llet id scr (
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
               Lifthenelse (lprim Pisint [scr], eint, etag)) in
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
       | `Neg, `Int -> lprim Pnegint [e]
       | `Neg, `Int32 -> lprim (Pnegbint Pint32) [e]
       | `Neg, `Int64 -> lprim (Pnegbint Pint64) [e]
       | `Neg, `Bigint -> builtin env ["Z"; "neg"] [e]
       | `Not, `Int -> lprim Pnot [e]
       | `Not, `Int32 ->
          lprim (Pxorbint Pint32) [e; Lconst ones32]
       | `Not, `Int64 ->
          lprim (Pxorbint Pint64) [e; Lconst ones64]
       | `Not, `Bigint -> builtin env ["Z"; "lognot"] [e] in
     code
  | Mintop2 (op, ((`Int|`Int32|`Int64) as ty), e1, e2) ->
     let e1 = to_lambda env e1 in
     let e2 = to_lambda env e2 in
     let prim = match ty with
       | `Int ->
          (match op with
            `Add -> Paddint | `Sub -> Psubint | `Mul -> Pmulint
#if OCAML_VERSION = (4, 03, 0)
          | `Div -> Pdivint | `Mod -> Pmodint
#else
          | `Div -> Pdivint Safe | `Mod -> Pmodint Safe
#endif
          | `And -> Pandint | `Or -> Porint | `Xor -> Pxorint
          | `Lsl -> Plslint | `Lsr -> Plsrint | `Asr -> Pasrint
          | `Lt -> Pintcomp Clt | `Gt -> Pintcomp Cgt
          | `Lte -> Pintcomp Cle | `Gte -> Pintcomp Cge
          | `Eq -> Pintcomp Ceq)
       | (`Int32 | `Int64) as ty ->
          let t = match ty with `Int32 -> Pint32  | `Int64 -> Pint64 in
          (match op with
            `Add -> Paddbint t | `Sub -> Psubbint t | `Mul -> Pmulbint t
#if OCAML_VERSION = (4, 03, 0)
          | `Div -> Pdivbint t | `Mod -> Pmodbint t
#else
          | `Div -> Pdivbint { size = t; is_safe = Safe }
          | `Mod -> Pmodbint { size = t; is_safe = Safe }
#endif
          | `And -> Pandbint t | `Or -> Porbint t | `Xor -> Pxorbint t
          | `Lsl -> Plslbint t | `Lsr -> Plsrbint t | `Asr -> Pasrbint t
          | `Lt -> Pbintcomp (t, Clt) | `Gt -> Pbintcomp (t, Cgt)
          | `Lte -> Pbintcomp (t, Cle) | `Gte -> Pbintcomp (t, Cge)
          | `Eq -> Pbintcomp (t, Ceq)) in
     lprim prim [e1; e2]
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
  | Mconvert (src, dst, e) ->
     let e = to_lambda env e in
     begin match src, dst with
       | `Bigint, `Bigint
       | `Int, `Int
       | `Int32, `Int32
       | `Int64, `Int64 -> e
       | `Bigint, ((`Int|`Int32|`Int64) as dst) ->
          (* Zarith raises exceptions on overflow, but we truncate conversions. Not fast. *)
          let width = match dst with 
            | `Int -> Sys.word_size - 1
            | `Int32 -> 32
            | `Int64 -> 64 in
          let range_id = Ident.create "range" in
          let range = Z.(shift_left (of_int 1) width) in
          let masked_id = Ident.create "masked" in
          let truncated =
            llet range_id 
                 (builtin env ["Z"; "of_string"] [Lconst (Const_immstring (Z.to_string range))])
            (llet masked_id
                 (builtin env ["Z"; "logand"] [e;
                      builtin env ["Z"; "sub"] [Lvar range_id;
                                                Lconst (Const_base (Const_int 1))]])
            (Lifthenelse (builtin env ["Z"; "testbit"] 
                                 [Lvar masked_id; Lconst (Const_base (Const_int (width - 1)))],
                         builtin env ["Z"; "sub"] [Lvar masked_id; Lvar range_id],
                         Lvar masked_id))) in
          let fn = match dst with
            | `Int -> "to_int"
            | `Int32 -> "to_int32"
            | `Int64 -> "to_int64" in
          builtin env ["Z"; fn] [truncated]
       | ((`Int|`Int32|`Int64) as src), `Bigint ->
          let fn = match src with
            | `Int -> "of_int"
            | `Int32 -> "of_int32"
            | `Int64 -> "of_int64" in
          builtin env ["Z"; fn] [e]
       | `Int, `Int32 ->
          lprim (Pbintofint Pint32) [e]
       | `Int, `Int64 ->
          lprim (Pbintofint Pint64) [e]
       | `Int32, `Int ->
          lprim (Pintofbint Pint32) [e]
       | `Int64, `Int ->
          lprim (Pintofbint Pint64) [e]
       | `Int32, `Int64 ->
          lprim (Pcvtbint(Pint32, Pint64)) [e]
       | `Int64, `Int32 ->
          lprim (Pcvtbint(Pint64, Pint32)) [e]
     end
  | Mvecnew (`Array, len, def) ->
     builtin env ["Array"; "make"] [to_lambda env len; to_lambda env def]
  | Mvecnew (`Bytevec, len, def) ->
     builtin env ["String"; "make"] [to_lambda env len; to_lambda env def]
  | Mvecget (ty, vec, idx) ->
     let prim = match ty with
       | `Array -> Parrayrefs Paddrarray
#if OCAML_VERSION = (4, 03, 0)
       | `Bytevec -> Pstringrefs
#else
       | `Bytevec -> Pbytesrefs
#endif
(*       | `Floatvec -> Parrayrefs Pfloatarray *) in
     lprim prim [to_lambda env vec; to_lambda env idx]
  | Mvecset (ty, vec, idx, v) ->
     let prim = match ty with
       | `Array -> Parraysets Paddrarray
#if OCAML_VERSION = (4, 03, 0)
       | `Bytevec -> Pstringsets
#else
       | `Bytevec -> Pbytessets
#endif
(*       | `Floatvec -> Parraysets Pfloatarray *) in
     lprim prim [to_lambda env vec; to_lambda env idx; to_lambda env v]
  | Mveclen (ty, vec) ->
     let prim = match ty with
       | `Array -> Parraylength Paddrarray
#if OCAML_VERSION = (4, 03, 0)
       | `Bytevec -> Pstringlength
#else
       | `Bytevec -> Pbyteslength
#endif
(*       | `Floatvec -> Parraylength Pfloatarray *) in
     lprim prim [to_lambda env vec]
  | Mblock (tag, vals) ->
     lprim (pmakeblock tag Immutable) (List.map (to_lambda env) vals)
  | Mfield (idx, e) ->
      lprim (Pfield(idx)) [to_lambda env e]

and bindings_to_lambda env bindings body =
  List.fold_right (fun b rest -> match b with
  | `Unnamed e ->
     Lsequence (to_lambda env e, rest)
  | `Named (n, e) ->
     llet n (to_lambda env e) rest
  | `Recursive bs ->
     Lletrec (List.map (fun (n, e) -> (n, to_lambda env e)) bs, rest))
    bindings body


let setup_options options =
  Clflags.native_code := true;
  Clflags.flambda_invariant_checks := true;
  Clflags.nopervasives := true;
  Clflags.dump_lambda := false;
  Clflags.dump_cmm := false;
  Clflags.keep_asm_file := false;
  Clflags.include_dirs := [Findlib.package_directory "zarith"];
  Clflags.inlining_report := false;
  Clflags.dlcode := true;
  Clflags.shared := false;

  Clflags.(
    default_simplify_rounds := 2;
    use_inlining_arguments_set o2_arguments;
    use_inlining_arguments_set ~round:0 o1_arguments);


  (* Hack: disable the "no cmx" warning for zarith *)
  Warnings.parse_options false "-58";
  assert (not (Warnings.is_active (Warnings.No_cmx_file "asdf")));

  (options |> List.iter @@ function
  | `Verbose ->
     Clflags.dump_lambda := true;
     Clflags.dump_cmm := true;
     Clflags.keep_asm_file := true;
     Clflags.inlining_report := true
  | `Shared ->
     Clflags.shared := true);

  Compenv.(readenv Format.std_formatter (Before_compile "malfunction"));
  Compmisc.init_path true


let module_to_lambda ?options (Mmod (bindings, exports)) =
  setup_options (match options with Some o -> o | None -> []);
  let print_if flag printer arg =
    if !flag then Format.printf "%a@." printer arg;
    arg in

  let env = Compmisc.initial_env () in
  let code =
    bindings_to_lambda env (reorder_bindings bindings)
      (lprim (pmakeblock 0 Immutable) (List.map (fun e -> to_lambda env (snd (reorder e))) exports)) in

  let lambda = code
  |> print_if Clflags.dump_rawlambda Printlambda.lambda
#if OCAML_VERSION = (4, 03, 0)
  |> Simplif.simplify_lambda
#else
  |> Simplif.simplify_lambda "malfunction"
#endif
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
  cmxfile : string;
  cmifile : string option
}


type lambda_mod = int * Lambda.lambda

let delete_temps { objfile; cmxfile; cmifile } =
  Misc.remove_file objfile;
  Misc.remove_file cmxfile;
  match cmifile with Some f -> Misc.remove_file f | None -> ()


type options = [`Verbose | `Shared] list


let lambda_to_cmx ?(options=[]) filename prefixname (size, code) =
  let ppf = Format.std_formatter in
  let outfiles = ref {
    cmxfile = prefixname ^ ".cmx";
    objfile = prefixname ^ Config.ext_obj;
    cmifile = None
  } in
  setup_options options;
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
           let chop_ext =
             #if OCAML_VERSION = (4, 03, 0)
               Misc.chop_extension_if_any
             #else
               Misc.chop_extensions
             #endif
             in
           let mlifile = chop_ext filename ^ !Config.interface_suffix in
           if Sys.file_exists mlifile then
             Typemod.(raise(Error(Location.in_file filename,
                                  Env.empty,
                                  Interface_not_compiled cmi)))
           else
             (* hackily generate an empty cmi file *)
             let cmifile = String.uncapitalize_ascii cmi in
             outfiles := { !outfiles with cmifile = Some cmifile };
             let mlifile = String.uncapitalize_ascii (modulename ^ ".mli") in
             let ch = open_out mlifile in
             output_string ch "(* autogenerated mli for malfunction *)\n";
             close_out ch;
             ignore (Sys.command ("ocamlc -c " ^ mlifile));
             Misc.remove_file mlifile;
             if not (Sys.file_exists cmifile) then failwith "Failed to generate empty cmi file";
             Env.read_signature modulename cmifile);
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
#if OCAML_VERSION > (4, 03, 0)
        (* FIXME: may need to add modules referenced only by "external" to this *)
        ~required_globals:(Ident.Set.of_list (Env.get_required_globals ()))
#endif
        ppf;
    Compilenv.save_unit_info !outfiles.cmxfile;
    Warnings.check_fatal ();
    !outfiles
  with e ->
    delete_temps !outfiles;
    raise e


let compile_cmx ?(options=[]) filename =
  let prefixname = Compenv.output_prefix filename in
  let lexbuf = Lexing.from_channel (open_in filename) in
  Lexing.(lexbuf.lex_curr_p <-
            { lexbuf.lex_curr_p with pos_fname = filename });
  Malfunction_parser.read_module lexbuf
  |> module_to_lambda ~options
  |> lambda_to_cmx ~options filename prefixname


(* copied from opttoploop.ml *)
type res = Ok of Obj.t | Err of string
external ndl_run_toplevel: string -> string -> res
  = "caml_natdynlink_run_toplevel"
external ndl_loadsym: string -> Obj.t = "caml_natdynlink_loadsym"

let code_id = ref 0

let compile_and_load ?(options : options =[]) e =
  if not Dynlink.is_native then
    failwith "Loading malfunction values works only in native code";
  let tmpdir = Filename.temp_file "malfunction" ".tmp" in
  (* more than a little horrible *)
  Unix.unlink tmpdir;
  Unix.mkdir tmpdir 0o700;
  incr code_id;
  let modname = "Malfunction_Code_" ^ string_of_int (!code_id) in
  let prefix = tmpdir ^ Filename.dir_sep ^ String.uncapitalize_ascii modname in
  let options = `Shared :: options in
  let tmpfiles =
    Mmod([], [e])
    |> module_to_lambda ~options
    |> lambda_to_cmx ~options "code" prefix in
  let cmxs = prefix ^ ".cmxs" in
  Asmlink.link_shared Format.err_formatter [tmpfiles.cmxfile] cmxs;
  delete_temps tmpfiles;
  (match ndl_run_toplevel cmxs modname with
  | Ok _ -> ()
  | Err s -> failwith ("loading failed: " ^ s));
  Misc.remove_file cmxs;
  Unix.rmdir tmpdir;
  Obj.field (ndl_loadsym (Compilenv.symbol_for_global (Ident.create_persistent modname))) 0



let link_executable output tmpfiles =
  (* urgh *)
  Sys.command (Printf.sprintf "ocamlfind ocamlopt -package zarith zarith.cmxa '%s' -o '%s'"
                 tmpfiles.cmxfile output)
