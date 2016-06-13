open Malfunction_parser

type value =
| Block of int * value array
| Seq of sequence_type * mutability * value array
| Func of (value -> value)
| Int of intconst

val eval : t -> value

