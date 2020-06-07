# Missing compiler primitives

If you ever run into a Malfunction error like the following,
```
Fatal error: exception Failure("unimplemented primitive %primitive")
```
you can fix it as follows:

1. find `translprim.ml` somewhere in `~/.opam`
2. search for your `%primitive` there and see how it's defined
3. add the definition into the match expression [starting around line 318 in the source](https://github.com/stedolan/malfunction/blob/master/src/malfunction_compiler.ml#L318)
4. `duna build` to check if it builds
5. commit
6. `opam reinstall malfunction` to reinstall Malfunction with your patch
7. send a pull request! :)
