(* Staged compilation of primitive-recursive arithmetic *)

type zero = [`Zero]
type 'a suc = [`Suc of 'a]

type _ v =
| ZV : ('a suc) v
| SV : 'a v -> ('a suc) v

type _ ctx =
| Eps : zero ctx
| Cons : 'a ctx * Z.t -> ('a suc) ctx

type 'a t =
| K : Z.t -> 'a t
| S : 'a t -> 'a t
| V : 'a v -> 'a t
| Let : 'a t * ('a suc) t -> 'a t
| Rec : {name : string; ifzero : 'a t; ifsuc : ('a suc suc) t; n : 'a t} -> 'a t


let v0 = V ZV
let v1 = V (SV ZV)
let v2 = V (SV (SV ZV))
let v3 = V (SV (SV (SV ZV)))
let v4 = V (SV (SV (SV (SV ZV))))

let (%) f x = Let(x, f)

let add () = Rec {name = "+"; ifzero = v1; ifsuc = S v1; n = v0}
let mul () = Rec {name = "*"; ifzero = K Z.zero; ifsuc = add () % v4 % v1; n = v0}
let exp () = Rec {name = "^"; ifzero = K Z.one; ifsuc = mul () % v4 % v1; n = v0}



let rec interpret : type k . k t -> k ctx -> Z.t =
  fun t env -> let open Z in
  match t with
  | K n ->
     n
  | S t ->
     add (interpret t env) one
  | V v ->
     let rec lookup : type k . k ctx -> k v -> Z.t =
       fun env var -> match var, env with
       | ZV, Cons (env, n) -> n
       | SV v, Cons (env, _) -> lookup env v in
     lookup env v
  | Let (e, body) ->
     interpret body (Cons (env, interpret e env))
  | Rec {name; ifzero; ifsuc; n} ->
     let n = interpret n env in
     let rec go n' fn' =
       if equal n n' then fn' else
         let env = Cons (Cons (env, fn'), n') in
         go (add n' one) (interpret ifsuc env) in
     go zero (interpret ifzero env)

(*
     let rec go n =
       if equal n zero then
         interpret ifzero env
       else
         let n = sub n one in
         let fn = go n in
         let env = Cons (Cons (env, fn), n) in
         interpret ifsuc env in
     go (interpret n env) *)

type 'a menv =
| Params : Malfunction.t -> 'a menv
| Local : 'a menv * Malfunction.t -> ('a suc) menv

let rec compile : type k . k t -> k menv -> Malfunction.t = 
  fun t env -> let open Z in let open Malfunction in
  match t with
  | K n ->
     Mint (`Bigint n)
  | S t ->
     Mintop2 (`Add, `Bigint, compile t env, Mint (`Bigint (Z.one)))
  | V v ->
     let rec lookup : type k . k menv -> k v -> Malfunction.t =
       fun env var -> match var, env with
       | ZV, Params env -> Mfield(1, env)
       | SV v, Params env -> lookup (Params (Mfield (0, env))) v
       | ZV, Local (env, v) -> v
       | SV v, Local (env, _) -> lookup env v in
     lookup env v
  | Let (e, body) ->
     bind_val (compile e env) @@ fun v ->
     compile body (Local (env, v))
  | Rec {name; ifzero; ifsuc; n} ->
     bind_val (compile n env) @@ fun n ->
     bind_rec (fun go -> lambda2 @@ fun n' fn' ->
       if_ (Mintop2(`Eq, `Bigint, n, n'))
         fn'
         (let env = Local(Local(env, fn'), n') in
          Mapply(go, [Mintop2(`Add, `Bigint, n', Mint (`Bigint Z.one));
                      compile ifsuc env]))) @@ fun go ->
     Mapply(go, [Mint (`Bigint Z.zero); compile ifzero env])


let run_compiled : type k . k t -> k ctx -> Z.t =
  fun t ->
    let code = Malfunction.(lambda @@ fun v -> compile t (Params v)) in
    let e = Malfunction_compiler.compile_and_load ~options:[`Verbose] code in
    fun env -> Obj.magic e env


(* testcase: compute 16^4 *)
let env = Cons(Cons(Eps, Z.of_int 16), Z.of_int 4)

let _ =
  assert (interpret (exp ()) env = Z.of_int 65536);
  assert (run_compiled (exp ()) env = Z.of_int 65536)

let benchmark name exec =
  let env = Cons(Cons(Eps, Z.of_int 16), Z.of_int 4) in
  let tstart = Unix.gettimeofday () in
  for i = 1 to 1000 do ignore (Sys.opaque_identity exec env) done;
  let tend = Unix.gettimeofday () in
  Printf.printf "%s: %f secs\n%!" name (tend -. tstart)

let _ =
  benchmark "interpreted" (interpret (exp ()));
  benchmark "compiled" (run_compiled (exp ()))



