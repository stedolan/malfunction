#!/usr/bin/env ocaml
#use "topfind"
#require "topkg"
open Topkg

let () = Pkg.describe "malfunction" (fun c ->
  Ok [Pkg.mllib "src/malfunction.mllib";
      Pkg.test ~args:(Cmd.((v "docs/spec.md") %% (v "test"))) "src/test";
      Pkg.bin "src/main" ~dst:"malfunction"])
