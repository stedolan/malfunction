#!/bin/bash

> test.expect
> test.log
exec >test.log 2>&1
expect () { echo "$@" >> test.expect; }
expect_ () { cat >> test.expect; }

ignore_linker_warnings () {
  # 32-bit debian and some osx versions issue spurious linker warnings
  # see https://github.com/ocaml/opam-repository/issues/3000 and 9728
  grep -v 'ld:.* warning:'
}

malfunction compile helloworld.mlf |& ignore_linker_warnings
./helloworld
expect 'Hello, world!'

malfunction compile -o foo helloworld.mlf |& ignore_linker_warnings
./foo
expect 'Hello, world!'

malfunction cmx helloworld.mlf
ocamlopt helloworld.cmx -o exec |& ignore_linker_warnings
./exec
expect 'Hello, world!'

ocamlc -opaque -c module.mli
malfunction cmx module.mlf
ocamlopt module.cmx main.ml -o main |& ignore_linker_warnings
./main
expect_ <<EOF
42
10
true false
111
EOF
