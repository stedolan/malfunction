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

type block_tag = private int
val max_tag : block_tag
val tag_of_int : int -> block_tag


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
  [ `Unnamed of t | `Named of Ident.t * t | `Recursive of (Ident.t * t) list ]

and case = [`Tag of int | `Deftag | `Intrange of int * int]

type moduleexp =
| Mmod of binding list * t list

(* Read the next expression from a lexbuf *)
val read_expression : Lexing.lexbuf -> t

(* Read an entire module from a lexbuf (must be followed by EOF) *)
val read_module : Lexing.lexbuf -> moduleexp
