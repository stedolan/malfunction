#!/usr/bin/env ocaml
#use "topfind"
#require "topkg"
open Topkg

let () = Pkg.describe "malfunction" (fun c ->
  Ok [Pkg.mllib "src/malfunction.mllib";
      Pkg.bin "src/main" ~dst:"malfunction"])
