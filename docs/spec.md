# Syntax and semantics of Malfunction

**Note**: This "specification" is preliminary at best, and subject to
  change when bugs are found, features are added, or I'm bored.

Malfunction does only very basic checking of syntax when loading a
program. For any program which passes the syntax checker, Malfunction
should do one of the following:
  - Report it as having undefined behaviour in the interpreter (`malfunction eval`)
  - Produce exactly the same result in the intepreter (`malfunction eval`) and compiler (`malfunction compile`)
  - Fail to terminate in either the interpreter or the compiler

The behaviour of the interpreter/compiler should agree with the text
below, although for a more precise specification you should look at
the
[definition of the interpreter](../src/malfunction_interpreter.ml),
which is straightforward (no bytecode or other efficiency tricks, just
syntax-directed execution).

It's not necessarily a bug in Malfunction if a program compiles with
`malfunction compile` and then crashes at runtime. This specification
intentionally leaves much behaviour undefined, so you should count
yourself lucky if a program like `(field 0 0)` is well-behaved enough
to merely crash.

However, the interpreter should detect *all* undefined behaviour
(Malfunction's semantics are kept quite simple to ensure that this is
easily semi-decidable). If a program runs to completion in the
intepreter producing a result, it is a bug in Malfunction if the
compiled version of the same program either crashes or produces a
different value, and [should be reported](https://github.com/stedolan/malfunction/issues).

This doesn't apply to programs which link with OCaml code: if you use
`(global ...)` to call an OCaml function, it's up to you to ensure
that you pass inputs that won't make it crash, and the interpreter
will (currently) be of no help checking this.

This file contains various examples of expected output of sample
programs. These are run as part of the testsuite, as are the other
programs in the [test directory](../test).

## Basic syntax

## Values

## Functions and evaluation order

lambda
apply
curried
at least one argument

## Integers and arithmetic

## Bindings

let
letrec
seq

## Blocks and fields

## Conditionals

## Vectors

## Accessing OCaml values

global
interpreter caveat
