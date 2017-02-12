#!/usr/bin/env ocaml
#use "topfind"
#require "topkg"
open Topkg

let () = Pkg.describe "malfunction" 
  ~build:(Pkg.build ~cmd:(fun c os files ->
    OS.Cmd.run @@ Cmd.(Pkg.build_cmd c os % "-plugin-tag" % "package(cppo_ocamlbuild)" %% of_list files)
  ) ())
  (fun c ->
  Ok [Pkg.mllib "src/malfunction.mllib";
      Pkg.test ~args:(Cmd.((v "docs/spec.md") %% (v "test"))) "src/test";
      Pkg.bin "src/malfunction_main" ~dst:"malfunction"])
