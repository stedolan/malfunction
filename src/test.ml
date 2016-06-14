open Malfunction_parser
open Malfunction_interpreter

let rec reify = function
| Block (n, xs) -> reify_block n xs
| Seq (`Array, _, xs) -> reify_block 0 xs
| Seq (`Bytevec, _, xs) ->
   let to_char = function
     | Int (`Int n) when 0 <= n && n < 256 ->
        String.make 1 (Char.chr n)
     | _ -> failwith "reify: noncharacter in string" in
   Obj.repr (String.concat "" (List.map to_char (Array.to_list xs)))
| Int n -> Obj.(match n with
  | `Int n -> repr n
  | `Int32 n -> repr n
  | `Int64 n -> repr n
  | `Bigint n -> repr n)
| Func _ -> failwith "reify: functional value"

and reify_block n xs =
  let o = Obj.new_block n (Array.length xs) in
  Array.iteri (Obj.set_field o) (Array.map reify xs);
  o
  

let equiv a b =
  eval a = eval b

