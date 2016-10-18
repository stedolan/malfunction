
type inttype = [`Int | `Int32 | `Int64 | `Bigint]
type intconst = [`Int of int | `Int32 of Int32.t | `Int64 of Int64.t | `Bigint of Z.t]
type unary_int_op =
  [`Neg | `Not]
type binary_int_op =
  [ `Add | `Sub | `Mul | `Div | `Mod
  | `And | `Or | `Xor | `Lsl | `Lsr | `Asr
  | `Lt | `Gt | `Lte | `Gte | `Eq ]

type vector_type =
  [`Array | `Bytevec]
type mutability =
  [ `Imm | `Mut ]

type block_tag = int

type case = [`Tag of int | `Deftag | `Intrange of int * int]


let max_tag = 200
let tag_of_int n =
  if 0 <= n && n < max_tag then
    n
  else
    invalid_arg "tag out of range"



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
| Mconvert of inttype * inttype * t

(* Vectors *)
| Mvecnew of vector_type * t * t
| Mvecget of vector_type * t * t
| Mvecset of vector_type * t * t * t
| Mveclen of vector_type * t

(* Blocks *)
| Mblock of int * t list
| Mfield of int * t

and binding =
  [ `Unnamed of t | `Named of Ident.t * t | `Recursive of (Ident.t * t) list ]


type var = Ident.t

let fresh n = Ident.create n

let bind_val e body =
  let v = fresh "x" in
  Mlet ([`Named (v, e)], body (Mvar v))

let bind_rec e body =
  let v = fresh "x" in
  Mlet ([`Recursive [v, e (Mvar v)]], body (Mvar v))

let tuple xs = Mblock(0, xs)

let lambda f =
  let v = fresh "x" in
  Mlambda ([v], f (Mvar v))

let lambda2 f =
  let vx = fresh "x" and vy = fresh "y" in
  Mlambda ([vx; vy], f (Mvar vx) (Mvar vy))

let if_ c tt ff =
  Mswitch (c, [[`Intrange(0,0)], ff; [`Intrange(min_int,max_int);`Deftag], tt])

module IntArith = struct
  let of_int n = Mint (`Int n)
  let zero = of_int 0
  let one = of_int 1
  let (~-) a = Mintop1(`Neg, `Int, a)
  let lnot a = Mintop1(`Not, `Int, a)
  let (+) a b = Mintop2(`Add, `Int, a, b)
  let (-) a b = Mintop2(`Sub, `Int, a, b)
  let ( * ) a b = Mintop2(`Mul, `Int, a, b)
  let (/) a b = Mintop2(`Div, `Int, a, b)
  let (mod) a b = Mintop2(`Mod, `Int, a, b)
  let (land) a b = Mintop2(`And, `Int, a, b)
  let (lor) a b = Mintop2(`Or, `Int, a, b)
  let (lxor) a b = Mintop2(`Xor, `Int, a, b)
  let (lsl) a b = Mintop2(`Lsl, `Int, a, b)
  let (lsr) a b = Mintop2(`Lsr, `Int, a, b)
  let (asr) a b = Mintop2(`Asr, `Int, a, b)
  let (<) a b = Mintop2(`Lt, `Int, a, b)
  let (>) a b = Mintop2(`Gt, `Int, a, b)
  let (<=) a b = Mintop2(`Lte, `Int, a, b)
  let (>=) a b = Mintop2(`Gte, `Int, a, b)
  let (=) a b = Mintop2(`Eq, `Int, a, b)
end

let with_error_reporting ppf def f =
  try f () with
  | Malfunction_sexp.SyntaxError ((locstart, locend), msg) ->
     let open Lexing in
     if locstart.pos_lnum = locend.pos_lnum then
       Format.fprintf ppf "%s:%d:%d-%d: %s\n%!"
         locstart.pos_fname locstart.pos_lnum (locstart.pos_cnum - locstart.pos_bol) (locend.pos_cnum - locend.pos_bol) msg
     else
       Format.fprintf ppf "%s:%d:%d-%d:%d %s\n%!"
         locstart.pos_fname locstart.pos_lnum (locstart.pos_cnum - locstart.pos_bol) locend.pos_lnum (locend.pos_cnum - locend.pos_bol) msg;
     def
  | x ->
     Location.report_exception ppf x;
    def

