open Sexp
open Lambda
open Asttypes


type inttype = [`Int | `Int32 | `Int64 | `Bigint]
type intconst = [`Int of int | `Int32 of Int32.t | `Int64 of Int64.t | `Bigint of Z.t]
type unary_int_op =
  [`Neg | `Not]
type binary_int_op =
  [ `Add | `Sub | `Mul | `Div | `Mod
  | `And | `Or | `Xor | `Lsl | `Lsr | `Asr
  | `Lt | `Gt | `Lte | `Gte | `Eq ]

type sequence_type =
  [`Array | `Bytevec | `Floatvec]
type mutability =
  [ `Imm | `Mut ]

(* Always well-scoped by construction *)
type t =
| Mvar of Ident.t
| Mlambda of Ident.t list * t
| Mapply of t * t list
| Mlet of binding list * t
| Mint of intconst
| Mstring of string
| Mglobal of Longident.t
| Mswitch of t * (case list * t) list

(* Integers *)
| Mintop1 of unary_int_op * inttype * t
| Mintop2 of binary_int_op * inttype * t * t

(* Sequences *)
| Mseqget of sequence_type * t * t
| Mseqset of sequence_type * t * t * t
| Mseqlen of sequence_type * t

(* Blocks *)
| Mblock of int * t list
| Mfield of int * t

and binding =
| Unnamed of t
| Named of Ident.t * t
| Recursive of (Ident.t * t) list

and case = [`Tag of int | `Deftag | `Intrange of int * int]

type moduleexp =
| Mmod of binding list * t list

(* Compiling from sexps *)

let fail loc fmt =
  let k ppf =
    raise (SyntaxError (loc, Format.flush_str_formatter ())) in
  Format.kfprintf k Format.str_formatter ("@[" ^^ fmt ^^ "@]")

module StrMap = Map.Make (struct type t = string let compare = compare end)

let bind_local loc locals s ident =
  StrMap.add s ident locals

let parse_arglist = function
  | loc, List args ->
     let idents = args |> List.map (function
       | loc, Var s ->
          s, Ident.create s
       | loc, _ -> fail loc "Expected a list of variables") in
     let env = List.fold_left (fun env (s, ident) ->
       if StrMap.mem s env then
         fail loc "Parameter %s bound multiple times" s
       else
         bind_local loc env s ident) StrMap.empty idents in
     List.map snd idents, env
  | loc, _ -> fail loc "Expected a list of atoms"

let parse_loc loc =
  Location.none

let max_tag = 200
let parse_tag = function
| loc, List [_, Atom "tag"; _, Int n] ->
   if 0 <= n && n < max_tag then n else fail loc "tag %d out of range [0,%d]" n (max_tag-1)
| loc, _ -> fail loc "invalid tag"

let unary_intops_by_name, binary_intops_by_name =
  let unary_ops = [ `Neg, "neg"; `Not, "not"; `Const, "i" ] in
  let binary_ops =
    [ `Add, "+" ; `Sub, "-" ; `Mul, "*" ; `Div, "/" ; `Mod, "%" ;
      `And, "&" ; `Or, "|" ; `Xor, "^" ; `Lsl, "<<" ; `Lsr, ">>"  ; `Asr, "a>>" ;
      `Lt, "<" ; `Gt, ">" ; `Lte, "<=" ; `Gte, ">=" ; `Eq, "==" ] in
  let types = [`Int, "" ; `Int32, "32" ; `Int64, "64" ; `Bigint, "big"] in
  let () = (* check that all cases are handled here *)
    List.iter (function (`Const | #unary_int_op), _ -> () | _ -> assert false) unary_ops;
    List.iter (function #binary_int_op, _ -> () | _ -> assert false) binary_ops;
    List.iter (function #inttype, _ -> () | _ -> assert false) types in
  List.fold_right (fun (ty,tyname) ->
    List.fold_right (fun (op,opname) ->
      StrMap.add (opname ^ tyname) (op, ty)) unary_ops) types StrMap.empty,
  List.fold_right (fun (ty,tyname) ->
    List.fold_right (fun (op,opname) ->
      StrMap.add (opname ^ tyname) (op, ty)) binary_ops) types StrMap.empty

let seqops_by_name op =
  List.fold_right (fun (ty,tyname) ->
    StrMap.add (op ^ "-" ^ tyname) ty)
    [`Array, "array"; `Bytevec, "bytevec"; `Floatvec, "floatvec"]
    StrMap.empty
let seq_get_by_name = seqops_by_name "get"
let seq_set_by_name = seqops_by_name "set"
let seq_len_by_name = seqops_by_name "len"

(*
(let
  (a 42)
  (b 17)
  (_ 421)
  (rec (a (lambda)))

*)

let rec parse_bindings loc env acc = function
  | [e] ->
     List.rev acc, env, e
  | (loc, List [_, Atom "_"; e]) :: bindings ->
     parse_bindings loc env (Unnamed (parse_exp env e) :: acc) bindings
  | (loc, List [_, Var s; e]) :: bindings ->
     let ident = Ident.create s in
     let env' = bind_local loc env s ident in
     parse_bindings loc env' (Named (ident, parse_exp env e) :: acc) bindings
  | (loc, List ((_, Atom "rec") :: recs)) :: bindings ->
     let recs = recs |> List.map (function
       | _, List [_, Var s; _, List ((_, Atom "lambda") :: _) as e] ->
          (s, Ident.create s, e)
       | _, List [_, Var s; _] ->
          fail loc "all members of a recursive binding must be functions"
       | loc, _ ->
          fail loc "expected recursive bindings") in
     let env' = List.fold_left (fun env (s, id, e) ->
       bind_local loc env s id) env recs in
     let recs = recs |> List.map (fun (s, id, e) ->
       (id, parse_exp env' e)) in
     parse_bindings loc env' (Recursive recs :: acc) bindings
  | _ -> fail loc "no bindings?"

and parse_exp env (loc, sexp) = match sexp with
  | Var s when StrMap.mem s env ->
     Mvar (StrMap.find s env)

  | Var s ->
     fail loc "'%s' is unbound" s

  | List [_, Atom "lambda"; args; exp] ->
     let (params, newenv) = parse_arglist args in
     let env = StrMap.fold StrMap.add newenv env in
     Mlambda (params, parse_exp env exp)

  | List ((loc, Atom "apply") :: func :: args) ->
     Mapply (parse_exp env func, List.map (parse_exp env) args)

  | List ((loc, Atom "let") :: bindings) ->
     let (bindings, env, e) = parse_bindings loc env [] bindings in
     Mlet (bindings, parse_exp env e)

  | List ((_, Atom "switch") :: exp :: cases) ->
     let parse_selector = function
       | _, List [_, Atom "tag"; _, Atom "_"] -> `Deftag
       | _, List ([_, Atom "tag"; _]) as t -> `Tag (parse_tag t)
       | _, Int n -> `Intrange (n, n)
       | _, List [_, Int min; _, Int max] -> `Intrange (min, max)
       | _, Atom "_" -> `Intrange (min_int, max_int)
       | loc, _ -> fail loc "invalid selector" in

     let rec parse_case loc acc = function
       | [s; e] -> List.rev (parse_selector s :: acc), parse_exp env e
       | (s :: c) -> parse_case loc (parse_selector s :: acc) c
       | _ -> fail loc "invalid case" in

     let cases = List.map (function
       | loc, List c -> parse_case loc [] c
       | loc, _ -> fail loc "invalid case") cases in

     if (List.length (List.sort_uniq compare cases) <> List.length cases) then
       fail loc "duplicate cases";

     Mswitch (parse_exp env exp, cases)

  | List [_, Atom s; e] when StrMap.mem s unary_intops_by_name ->
     let validate_const (pi, ps) = function
       | _, Int n -> Mint (pi n)
       | loc, Atom s -> (try Mint (ps s) with Failure _ | Invalid_argument _ -> 
         fail loc "invalid literal %s" s)
       | loc, _ -> fail loc "invalid literal" in
     let const_parser = function
       | `Int -> (fun x -> `Int x), (fun x -> `Int (int_of_string x))
       | `Int32 -> (fun x -> `Int32 (Int32.of_int x)), (fun x -> `Int32 (Int32.of_string x)) 
       | `Int64 -> (fun x -> `Int64 (Int64.of_int x)), (fun x -> `Int64 (Int64.of_string x))
       | `Bigint -> (fun x -> `Bigint (Z.of_int x)), (fun x -> `Bigint (Z.of_string x)) in
     begin match StrMap.find s unary_intops_by_name with
     | (`Neg | `Not) as op, ty -> Mintop1 (op, ty, parse_exp env e)
     | `Const, ty -> validate_const (const_parser ty) e
     end

  | List [_, Atom s; e1; e2] when StrMap.mem s binary_intops_by_name ->
     let (op, ty) = StrMap.find s binary_intops_by_name in
     Mintop2 (op, ty, parse_exp env e1, parse_exp env e2)

  | List [_, Atom op; seq; idx] when StrMap.mem op seq_get_by_name ->
     Mseqget (StrMap.find op seq_get_by_name, parse_exp env seq, parse_exp env idx)

  | List [_, Atom op; seq; idx; v] when StrMap.mem op seq_set_by_name ->
     Mseqset (StrMap.find op seq_set_by_name, parse_exp env seq, parse_exp env idx, parse_exp env v)

  | List [_, Atom op; seq] when StrMap.mem op seq_len_by_name ->
     Mseqlen (StrMap.find op seq_len_by_name, parse_exp env seq)

  | List ((_, Atom "block") :: tag :: fields) ->
     Mblock (parse_tag tag, List.map (parse_exp env) fields)

  | List [_, Atom "field"; _, Int n; e] ->
     Mfield (n, parse_exp env e)

  | Int k ->
     Mint (`Int k)
  | String s ->
     Mstring s

  | List ((_, Atom "global") :: path) ->
     Mglobal (path
       |> List.map (function
         | _, Var s -> s
         | _, _ -> fail loc "module path required")
       |> function
         | [] -> fail loc "empty global path"
         | path1 :: pathrest ->
            List.fold_left (fun id s ->
              Longident.Ldot (id, s)) (Longident.Lident path1) pathrest)

  | List ((_, Atom s) :: _) ->
     fail loc "Unknown operation %s" s

  | Atom s -> fail loc "bad syntax: %s" s

  | _ -> fail loc "syntax error"


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
         ap_loc = parse_loc loc;
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
     List.fold_right (fun b rest -> match b with
       | Unnamed e ->
          Lsequence (to_lambda env e, rest)
       | Named (n, e) ->
          Llet (Strict, n, to_lambda env e, rest)
       | Recursive bs ->
          Lletrec (List.map (fun (n, e) -> (n, to_lambda env e)) bs, rest))
       bindings (to_lambda env body)
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
                   | Some e -> max_tag
                   | None -> 1 + List.fold_left (fun s (`Tag i, e) -> max s i) (-1) tags in
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
       | `Floatvec -> Parrayrefs Pfloatarray in
     Lprim (prim, [to_lambda env seq; to_lambda env idx])
  | Mseqset (ty, seq, idx, v) ->
     let prim = match ty with
       | `Array -> Parraysets Paddrarray
       | `Bytevec -> Pstringsets
       | `Floatvec -> Parraysets Pfloatarray in
     Lprim (prim, [to_lambda env seq; to_lambda env idx; to_lambda env v])
  | Mseqlen (ty, seq) ->
     let prim = match ty with
       | `Array -> Parraylength Paddrarray
       | `Bytevec -> Pstringlength
       | `Floatvec -> Parraylength Pfloatarray in
     Lprim (prim, [to_lambda env seq])
  | Mblock (tag, vals) ->
     Lprim (Pmakeblock(tag, Immutable), List.map (to_lambda env) vals)
  | Mfield (idx, e) ->
     Lprim (Pfield(idx), [to_lambda env e])


type value =
| Block of int * value array
| Seq of sequence_type * mutability * value array
| Func of (value -> value)
| Val of Lambda.structured_constant
| Int of intconst

let rec interpret locals env : t -> value = function
  | Mvar v -> Ident.Map.find v locals
  | Mlambda (xs, e) ->
     let (x, e) = match xs with
       | [] -> assert false
       | [x] -> x, e
       | (x :: xs) -> x, Mlambda (xs, e) in
     Func (fun v -> interpret (Ident.Map.add x v locals) env e)
  | Mapply (f, vs) ->
     List.fold_left (fun f v -> match f with
     | Func f -> f (interpret locals env v)
     | _ -> failwith "not a function") (interpret locals env f) vs
  | Mlet (bindings, body) ->
     let rec bind locals = function
       | [] ->
          interpret locals env body
       | Unnamed e :: bindings ->
          ignore (interpret locals env e);
          bind locals bindings
       | Named (x, e) :: bindings ->
          let locals = Ident.Map.add x (interpret locals env e) locals in
          bind locals bindings
       | Recursive recs :: bindings ->
          let n = List.length recs in
          let values = Array.make n None in
          let locals = List.fold_right
            (fun (x, e) locals -> Ident.Map.add x e locals)
            (List.mapi (fun i (x, _) ->
              (x, Func (fun v -> match values.(i) with
              | Some (Func f) -> f v
              | _ -> failwith "bad recursive binding"))) recs)
            locals in
          recs |> List.iteri (fun i (_, e) ->
            values.(i) <- Some (interpret locals env e));
          bind locals bindings in
     bind locals bindings
  | Mint k -> Int k
  | Mstring s ->
     Seq (`Bytevec, `Imm, 
          Array.init (String.length s) (fun i -> Int (`Int (Char.code (String.get s i)))))
  | Mglobal v -> failwith "globals unsupported"
(*
     let (path, _descr) = Env.lookup_value v env in
     let rec lookup = function
       | Pident id -> Symtable.get_global_value id
*)
  | Mswitch (scr, cases) ->
     let scr = interpret locals env scr in
     let rec find_match = function
       | (cases, e) :: rest ->
          if List.exists (fun case -> match case, scr with
          | `Tag n, Block (n', _) -> n = n'
          | `Deftag, Block _ -> true
          | `Intrange (min, max), Val (Const_base (Asttypes.Const_int n)) -> min <= n && n <= max
          | _, _ -> false) cases then
            interpret locals env e
          else
            find_match rest
       | [] -> failwith "no case matches" in
     find_match cases
  | Mintop1 (op, ty, e) ->
     let v = match interpret locals env e with
       | Int k -> k | _ -> failwith "expected integer" in
     Int (match ty, op, v with
     | `Int, `Neg, `Int n -> `Int (~-n)
     | `Int, `Not, `Int n -> `Int (lnot n)
     | `Int32, `Neg, `Int32 n -> `Int32 (Int32.neg n)
     | `Int32, `Not, `Int32 n -> `Int32 (Int32.lognot n)
     | `Int64, `Neg, `Int64 n -> `Int64 (Int64.neg n)
     | `Int64, `Not, `Int64 n -> `Int64 (Int64.lognot n)
     | `Bigint, `Neg, `Bigint n -> `Bigint (Z.neg n)
     | `Bigint, `Not, `Bigint n -> `Bigint (Z.lognot n)
     | _ -> failwith "wrong integer type")
  | Mintop2 (op, ty, e1, e2) ->
     let (v1, v2) = match interpret locals env e1, interpret locals env e2 with
       | Int k1, Int k2 -> k1, k2
       | _ -> failwith "expected integers" in
     Int (failwith "unimplemented!")
  | Mseqget (ty, seq, idx) ->
     (match interpret locals env seq, interpret locals env idx with
     | Seq (ty', _, vals), Int (`Int i) when ty = ty' -> vals.(i)
     | _ -> failwith "wrong sequence type")
  | Mseqset (ty, seq, idx, e) ->
     (match interpret locals env seq, 
            interpret locals env idx, 
            interpret locals env e with
     | Seq (ty', `Mut, vals), Int (`Int i), v when ty = ty' ->
        vals.(i) <- v; Int (`Int 0)
     | _ -> failwith "wrong sequence type/mutability")
  | Mseqlen (ty, seq) ->
     (match interpret locals env seq with
     | Seq (ty', _, vals) when ty = ty' -> Int (`Int (Array.length vals))
     | _ -> failwith "wrong sequence type")
  | Mblock (tag, vals) ->
     Block (tag, Array.of_list (List.map (interpret locals env) vals))
  | Mfield (idx, b) ->
     (match interpret locals env b with
     | Block (_, vals) -> vals.(idx)
     | _ -> failwith "not a block")

let parse_mod (loc, sexp) = match sexp with
  | List ((_, Atom "module") :: rest) ->
     let (bindings, env, exports) = parse_bindings loc StrMap.empty [] rest in
     let exports = match exports with
       | _, List ((_, Atom "export") :: exports) ->
          List.map (parse_exp env) exports
       | _ -> fail loc "export list?" in
     Mmod (bindings, exports)
  | _ -> fail loc "mod?"

let lambda_of_mod (Mmod (bindings, exports)) =
  let code = Mlet (bindings, Mblock(0, exports)) in
  let globals = Compmisc.initial_env () in

  let print_if flag printer arg =
    if !flag then Format.printf "%a@." printer arg;
    arg in

  let lambda = code
  |> to_lambda globals
  |> print_if Clflags.dump_rawlambda Printlambda.lambda
  |> Simplif.simplify_lambda
  |> print_if Clflags.dump_lambda Printlambda.lambda in

  (List.length exports, lambda)
