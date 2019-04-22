  $ malfunction compile helloworld.mlf
  $ ./helloworld
  Hello, world!

  $ malfunction compile -o foo helloworld.mlf
  $ ./foo
  Hello, world!

  $ malfunction cmx helloworld.mlf
  $ ocamlopt helloworld.cmx -o exec
  $ ./exec
  Hello, world!

  $ ocamlc -opaque -c module.mli
  $ malfunction cmx module.mlf
  $ ocamlopt module.cmx main.ml -o main
  $ ./main
  42
  10
  true false
  111
