open Malfunction_parser

type value =
| Block of int * value array
| Vec of vector_type * value array
| Func of (value -> value)
| Int of intconst

exception Error of string

let fail fmt =
  let k ppf =
    raise (Error (Format.flush_str_formatter ())) in
  Format.kfprintf k Format.str_formatter ("@[" ^^ fmt ^^ "@]")

module type IntType = sig
  type t
  val of_int : int -> t
  val of_string : string -> t

  val neg : t -> t
  val lognot : t -> t

  val add : t -> t -> t
  val sub : t -> t -> t
  val mul : t -> t -> t
  val div : t -> t -> t
  val rem : t -> t -> t
  val logand : t -> t -> t
  val logor : t -> t -> t
  val logxor : t -> t -> t
  val shift_left : t -> int -> t
  val shift_right_logical : t -> int -> t
  val shift_right : t -> int -> t

  val compare : t -> t -> int

  val of_val : value -> t
  val to_val : t -> value
end

module IntTypeInt = struct
  type t = int
  let of_int x = x
  let of_string = int_of_string
  let neg = (~-)
  let lognot = (lnot)
  let add = (+)
  let sub = (-)
  let mul = ( * )
  let div = (/)
  let rem = (mod)
  let logand = (land)
  let logor = (lor)
  let logxor = (lxor)
  let shift_left = (lsl)
  let shift_right_logical = (lsr)
  let shift_right = (asr)
  let compare = compare

  let of_val = function
    | Int (`Int n) -> n
    | _ -> fail "expected int"
  let to_val n = Int (`Int n)
end

module Arith (I : IntType) = struct
  open I
  let unary_op op a = match op with
    | `Neg -> to_val (neg (of_val a))
    | `Not -> to_val (lognot (of_val a))

  type op_normal = [`Add|`Sub|`Mul|`Div|`Mod|`And|`Or|`Xor]
  type op_shift = [`Lsl|`Lsr|`Asr]
  type op_cmp = [`Lt|`Gt|`Lte|`Gte|`Eq]

  let binary_op op a b = match op with
    | #op_normal as op ->
       let a = of_val a and b = of_val b in
       to_val ((match op with
       | `Add -> add | `Sub -> sub
       | `Mul -> mul | `Div -> div | `Mod -> rem
       | `And -> logand | `Or -> logor | `Xor -> logxor) a b)
    | #op_shift as op ->
       let a = of_val a and k = IntTypeInt.of_val b in
       to_val ((match op with
       | `Lsl -> shift_left
       | `Lsr -> shift_right_logical
       | `Asr -> shift_right) a k)
    | #op_cmp as op ->
       let a = of_val a and b = of_val b in
       let int_of_bool x = Int (`Int (if x then 1 else 0)) in
       let cmp = compare a b in
       int_of_bool (match op with
       | `Lt -> cmp < 0
       | `Gt -> cmp > 0
       | `Lte -> cmp <= 0
       | `Gte -> cmp >= 0
       | `Eq -> cmp = 0)
end

module ArithInt = Arith(IntTypeInt)
module ArithInt32 = Arith(struct
  include Int32
  let of_val = function
    | Int (`Int32 n) -> n
    | _ -> fail "expected int32"
  let to_val n = Int (`Int32 n)
end)
module ArithInt64 = Arith(struct
  include Int64
  let of_val = function
    | Int (`Int64 n) -> n
    | _ -> fail "expected int64"
  let to_val n = Int (`Int64 n)
end)
module ArithBigint = Arith(struct
  include Z
  let shift_right_logical = shift_right
  let of_val = function
    | Int (`Bigint n) -> n
    | _ -> fail "expected bigint"
  let to_val n = Int (`Bigint n)
end)





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
     | _ -> fail "not a function") (interpret locals env f) vs
  | Mlet (bindings, body) ->
     let rec bind locals = function
       | [] ->
          interpret locals env body
       | `Unnamed e :: bindings ->
          ignore (interpret locals env e);
          bind locals bindings
       | `Named (x, e) :: bindings ->
          let locals = Ident.Map.add x (interpret locals env e) locals in
          bind locals bindings
       | `Recursive recs :: bindings ->
          let n = List.length recs in
          let values = Array.make n None in
          let locals = List.fold_right
            (fun (x, e) locals -> Ident.Map.add x e locals)
            (List.mapi (fun i (x, _) ->
              (x, Func (fun v -> match values.(i) with
              | Some (Func f) -> f v
              | _ -> fail "bad recursive binding"))) recs)
            locals in
          recs |> List.iteri (fun i (_, e) ->
            values.(i) <- Some (interpret locals env e));
          bind locals bindings in
     bind locals bindings
  | Mint k -> Int k
  | Mstring s ->
     Vec (`Bytevec,
          Array.init (String.length s) (fun i -> Int (`Int (Char.code (String.get s i)))))
  | Mglobal v -> fail "globals unsupported"
     (*
     let (path, _descr) = Env.lookup_value v env in
     let path = Env.normalize_path None env path in
     let rec lookup = let open Path in function
       | Pident id -> Symtable.get_global_value id
       | Pdot (path, _, i) -> Obj.field (lookup path) i
       | Papply _ -> fail "functor application in global reference" in
     lookup path
     *)
  | Mswitch (scr, cases) ->
     let scr = interpret locals env scr in
     let rec find_match = function
       | (cases, e) :: rest ->
          if List.exists (fun case -> match case, scr with
          | `Tag n, Block (n', _) -> n = n'
          | `Deftag, Block _ -> true
          | `Intrange (min, max), Int (`Int n) -> min <= n && n <= max
          | _, _ -> false) cases then
            interpret locals env e
          else
            find_match rest
       | [] -> fail "no case matches" in
     find_match cases
  | Mintop1 (op, ty, e) ->
     let fn = match ty with
       | `Int -> ArithInt.unary_op
       | `Int32 -> ArithInt32.unary_op
       | `Int64 -> ArithInt64.unary_op
       | `Bigint -> ArithBigint.unary_op in
     fn op (interpret locals env e)
  | Mintop2 (op, ty, e1, e2) ->
     let fn = match ty with
       | `Int -> ArithInt.binary_op
       | `Int32 -> ArithInt32.binary_op
       | `Int64 -> ArithInt64.binary_op
       | `Bigint -> ArithBigint.binary_op in
     fn op (interpret locals env e1) (interpret locals env e2)
  | Mvecnew (ty, len, def) ->
     (match ty, interpret locals env len, interpret locals env def with
     | `Array, Int (`Int len), v ->
        Vec (`Array, Array.make len v)
     | `Bytevec, Int (`Int len), (Int (`Int k) as v) when 0 <= k && k < 256 ->
        Vec (`Bytevec, Array.make len v)
     | _, _, _ -> fail "bad vector creation")
  | Mvecget (ty, vec, idx) ->
     (match interpret locals env vec, interpret locals env idx with
     | Vec (ty', vals), Int (`Int i) when ty = ty' ->
        if 0 <= i && i < Array.length vals then
          vals.(i)
        else
          fail "index out of bounds: %d" i
     | _ -> fail "wrong vector type")
  | Mvecset (ty, vec, idx, e) ->
     (match interpret locals env vec, 
            interpret locals env idx, 
            interpret locals env e with
     | Vec (ty', vals), Int (`Int i), v when ty = ty' ->
        if 0 <= i && i <= Array.length vals then begin
          (match ty, v with
          |  `Array, _ -> ()
          | `Bytevec, Int (`Int i) when 0 <= i && i < 256 -> ()
          | `Bytevec, v -> fail "not a byte");
          vals.(i) <- v; Int (`Int 0)
        end else
          fail "index out of bounds: %d" i
     | _ -> fail "wrong vector type")
  | Mveclen (ty, vec) ->
     (match interpret locals env vec with
     | Vec (ty', vals) when ty = ty' -> Int (`Int (Array.length vals))
     | _ -> fail "wrong vector type")
  | Mblock (tag, vals) ->
     Block (tag, Array.of_list (List.map (interpret locals env) vals))
  | Mfield (idx, b) ->
     (match interpret locals env b with
     | Block (_, vals) -> vals.(idx)
     | _ -> fail "not a block")

let eval exp =
  interpret Ident.Map.empty () exp

let loc =
  let l = Lexing.{pos_fname="<value>"; pos_lnum=0; pos_cnum=0; pos_bol=0} in
  l,l

let rec render_value = let open Malfunction_sexp in function
| Block (tag, elems) -> loc, List (
  (loc, Atom "block")::
  (loc, List [loc, Atom "tag"; loc, Int tag]):: 
  List.map render_value (Array.to_list elems))
| Vec (ty, vals) ->
  loc, List ((loc, Atom (match ty with `Array -> "vector" | `Bytevec -> "vector.byte"))::
              List.map render_value (Array.to_list vals))
| Func f ->
  loc, Atom "<function>"
| Int (`Int n) ->
  loc, Int n
| Int (`Int32 n) ->
  loc, List [loc, Atom "i.32"; loc, Atom (Int32.to_string n)]
| Int (`Int64 n) ->
  loc, List [loc, Atom "i.64"; loc, Atom (Int64.to_string n)]
| Int (`Bigint n) ->
  loc, List [loc, Atom "i.big"; loc, Atom (Z.to_string n)]

   
