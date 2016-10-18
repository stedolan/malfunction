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

type block_tag = private int

type case = [`Tag of int | `Deftag | `Intrange of int * int]

val max_tag : block_tag
val tag_of_int : int -> block_tag


type var = Ident.t

(* the argument to fresh does not affect semantics, but can be useful for debugging *)
val fresh : string -> var

type t =
| Mvar of var
| Mlambda of var list * t
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
  [ `Unnamed of t | `Named of var * t | `Recursive of (var * t) list ]

(* generate 'let' and 'let rec' in HOAS style *)
val bind_val : t -> (t -> t) -> t
val bind_rec : (t -> t) -> (t -> t) -> t

(* create a block of tag 0 *)
val tuple : t list -> t

val lambda : (t -> t) -> t
val lambda2 : (t -> t -> t) -> t

val if_ : t -> t -> t -> t

module IntArith : sig
  val zero : t
  val one : t
  val of_int : int -> t
  val (~-) : t -> t
  val lnot : t -> t
  val (+) : t -> t -> t
  val (-) : t -> t -> t
  val ( * ) : t -> t -> t
  val (/) : t -> t -> t
  val (mod) : t -> t -> t
  val (land) : t -> t -> t
  val (lor) : t -> t -> t
  val (lxor) : t -> t -> t
  val (lsl) : t -> t -> t
  val (lsr) : t -> t -> t
  val (asr) : t -> t -> t
  val (<) : t -> t -> t
  val (>) : t -> t -> t
  val (<=) : t -> t -> t
  val (>=) : t -> t -> t
  val (=) : t -> t -> t
end

(* utility function to catch errors from parsing and compilation *)
val with_error_reporting : Format.formatter -> 'a -> (unit -> 'a) -> 'a


