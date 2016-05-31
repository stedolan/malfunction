open Sexp
open Lambda
open Asttypes


type inttype = [`Unboxed | `Int32 | `Int64]
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
| Mconst of Lambda.structured_constant
| Mglobal of Longident.t
| Mswitch of t * cases

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

and cases = 
  { tagcases : (int * t) list * t option;
    intcases : (int * int * t) list }
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
| loc, List [_, Atom "tag"; _, Const (Const_base (Asttypes.Const_int n))] ->
   if 0 <= n && n < max_tag then n else fail loc "tag %d out of range [0,%d]" n (max_tag-1)
| loc, _ -> fail loc "invalid tag"

let unary_intops_by_name, binary_intops_by_name =
  let unary_ops = [ `Neg, "neg"; `Not, "not" ] in
  let binary_ops =
    [ `Add, "+" ; `Sub, "-" ; `Mul, "*" ; `Div, "/" ; `Mod, "%" ;
      `And, "&" ; `Or, "|" ; `Xor, "^" ; `Lsl, "<<" ; `Lsr, ">>"  ; `Asr, "a>>" ;
      `Lt, "<" ; `Gt, ">" ; `Lte, "<=" ; `Gte, ">=" ; `Eq, "==" ] in
  let types = [`Unboxed, "" ; `Int32, "32" ; `Int64, "64"] in
  let () = (* check that all cases are handled here *)
    List.iter (function #unary_int_op, _ -> () | _ -> assert false) unary_ops; 
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
     let add_case cases (_, s) = match cases, s with
       | { tagcases }, List [_, List ((_, Atom "tag") :: _) as tag; e] ->
          let t = parse_tag tag in
          if List.mem_assoc t tagcases then fail loc "Duplicate tag case %d" t;
          { cases with tagcases = (t, parse_exp env e) :: tagcases } 
       | { intcases }, List [_, Const (Const_base (Const_int n)); e] ->
          if List.mem_assoc n intcases then fail loc "Duplicate case %d" n;
          { cases with intcases = (n, parse_exp env e) :: intcases }
       | { defcase = None }, List [_, Atom "default"; e] ->
          { cases with defcase = Some (parse_exp env e) }
       | { defcase = Some _ }, List [_, Atom "default"; e] ->
          (* fail loc "Duplicate default cases" *)
          cases (* HACK *)
       | _, _ ->
          fail loc "Parse error in switch" in
     let cases = List.fold_left add_case { tagcases = []; intcases = []; defcase = None } cases in
     Mswitch (parse_exp env exp, cases)

  | List [_, Atom s; e] when StrMap.mem s unary_intops_by_name ->
     let (op, ty) = StrMap.find s unary_intops_by_name in
     Mintop1 (op, ty, parse_exp env e)

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

  | List [_, Atom "field"; _, Const (Const_base (Asttypes.Const_int n)); e] ->
     Mfield (n, parse_exp env e)

  | Const k ->
     Mconst k

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
     Lapply {
       ap_func = to_lambda env fn;
       ap_args = List.map (to_lambda env) args;
       ap_loc = parse_loc loc;
       ap_should_be_tailcall = false;
       ap_inlined = Default_inline;
       ap_specialised = Default_specialise;
     }
  | Mlet (bindings, body) ->
     List.fold_right (fun b rest -> match b with
       | Unnamed e ->
          Lsequence (to_lambda env e, rest)
       | Named (n, e) ->
          Llet (Strict, n, to_lambda env e, rest)
       | Recursive bs ->
          Lletrec (List.map (fun (n, e) -> (n, to_lambda env e)) bs, rest))
       bindings (to_lambda env body)
  | Mconst k ->
     Lconst k
  | Mglobal v ->
     let (path, _descr) = Env.lookup_value (* ~loc:(parse_loc loc) *) v env in
     Lambda.transl_path (* ~loc:(parse_loc loc) *) env path
  | Mswitch (scr, cases) ->
     let switch_tag scr (tags, def) =
       let numtags = match def with
         | Some e -> max_tag
         | None -> 1 + List.fold_left (fun s (i, e) -> max s i) (-1) tags in
       Lswitch (scr, {
         sw_numconsts = 0;
         sw_consts = [];
         sw_numblocks = numtags;
         sw_blocks = List.map (fun (i, e) -> i, to_lambda env e) tags;
         sw_failaction = match def with None -> None | Some e -> Some (to_lambda env e)
       }) in
     let scr = to_lambda env scr in
     let select int tag =
       let id = Ident.create "switch" in
       Llet (Strict, id, scr,
             Lifthenelse
               (Lprim (Pisint, [Lvar id]),
                int (Lvar id),
                tag (Lvar id))) in
     begin match cases with
     | { intcases = ([_, e], None) | ([], Some e); tagcases = [], None}
     | { intcases = [], None; tagcases = ([_, e], None) | ([], Some e) } ->
        (* only one case, don't bother testing *)
        to_lambda env e
     | { intcases = [0, ezero], None; tagcases = (([_, enz], None) | ([], Some enz)) }
     | { intcases = [0, ezero], Some enz; tagcases = [], None } ->
        (* two cases: 0 and something else, like with list or option types *)
        Lifthenelse (scr, to_lambda env enz, to_lambda env ezero)
     | { intcases ; tagcases = [], None } ->
        (* switch on integers *)
        switch_int scr intcases
     | { intcases = [], None; tagcases } ->
        (* switch on tags *)
        switch_tag scr tagcases
     | { intcases = ([_, eint], None) | ([], Some eint); 
         tagcases = ([_, etag], None) | ([], Some etag) } ->
        (* one int, one tag *)
        select (fun _ -> to_lambda env eint) (fun _ -> to_lambda env etag)
     | { intcases = ([_, eint], None) | ([], Some eint); tagcases } ->
        (* one int, some tags *)
        select (fun _ -> to_lambda env eint) (fun e -> switch_tag e tagcases)
     | { intcases; tagcases = ([_, etag], None) | [], Some etag } ->
        (* some ints, one tag *)
        select (fun e -> switch_int e intcases) (fun _ -> to_lambda env etag)
     | { intcases ; tagcases } ->
        (* some ints, some tags *)
        select (fun e -> switch_int e intcases) (fun e -> switch_tag e tagcases)
     end
(*

     Lswitch (to_lambda env e, {
       sw_numconsts = (* FIXME: explain *) 2 + List.fold_left (fun s (i, e) -> max s i) (-1) cases.intcases;
       sw_consts = List.map (fun (i, e) -> (i, to_lambda env e)) cases.intcases;
       sw_numblocks = max_tag;
       sw_blocks = List.map (fun (i, e) -> (i, to_lambda env e)) cases.tagcases;
       sw_failaction = match cases.defcase with None -> None | Some e -> Some (to_lambda env e)
     })*)
  | Mintop1 (op, ty, e) ->
     let e = to_lambda env e in
     let ones32 = Const_base (Asttypes.Const_int32 (Int32.of_int (-1))) in
     let ones64 = Const_base (Asttypes.Const_int64 (Int64.of_int (-1))) in
     let code = match op, ty with
       | `Neg, `Unboxed -> Lprim (Pnegint, [e])
       | `Neg, `Int32 -> Lprim (Pnegbint Pint32, [e])
       | `Neg, `Int64 -> Lprim (Pnegbint Pint64, [e])
       | `Not, `Unboxed -> Lprim (Pnot, [e])
       | `Not, `Int32 -> 
          Lprim (Pxorbint Pint32, [e; Lconst ones32])
       | `Not, `Int64 ->
          Lprim (Pxorbint Pint64, [e; Lconst ones64]) in
     code
  | Mintop2 (op, ty, e1, e2) ->
     let e1 = to_lambda env e1 in
     let e2 = to_lambda env e2 in
     let prim = match ty with
       | `Unboxed ->
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
| Block of value array
| Seq of sequence_type * mutability * value array
| Func of (value -> value)
| Val of Lambda.structured_constant

let rec interpret locals env = function
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
            values.(i) <- interpret locals env e);
          bind locals bindings in
     bind locals bindings
  | Mconst k -> Val k
  | Mglobal v -> failwith "globals unsupported"
(*
     let (path, _descr) = Env.lookup_value v env in
     let rec lookup = function
       | Pident id -> Symtable.get_global_value id
*)
  | Mswitch (scr, cases) ->
     begin match interpret locals env scr with
     | Val (Const_base (Const_int n)) ->
        (match List.assoc n cases.intcases with
        | e -> interpret locals env e
        | exception Not_found ->
           match cases.defcase with
           | Some e -> interpret locals env e
           | None -> failwith "no match")
     | _ -> failwith "no match"
     end
  | _ -> failwith "nope"


let parse_mod globals (loc, sexp) = match sexp with
  | List ((_, Atom "module") :: rest) ->
     let (bindings, env, exports) = parse_bindings loc StrMap.empty [] rest in
     let exports = match exports with
       | _, List ((_, Atom "export") :: exports) ->
          List.map (parse_exp env) exports
       | _ -> fail loc "export list?" in
     let code = Mlet (bindings, Mblock(0, exports)) in
     (List.length exports, to_lambda globals code)
  | _ -> fail loc "mod?"
