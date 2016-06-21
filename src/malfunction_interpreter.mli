open Malfunction_parser

exception Error of string

type value =
| Block of int * value array
| Seq of sequence_type * mutability * value array
| Func of (value -> value)
| Int of intconst

val eval : t -> value
val render_value : value -> Malfunction_sexp.sexp
