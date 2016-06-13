open Malfunction_parser

type value =
| Block of int * value array
| Seq of sequence_type * mutability * value array
| Func of (value -> value)
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
          | `Intrange (min, max), Int (`Int n) -> min <= n && n <= max
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
