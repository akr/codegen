# codegen plugin for Coq

This software provides Coq commands to generate C source code
from Gallina definitions.

## Home page

https://github.com/akr/codegen

## Features

- Gallina to C translation
- Monomorphization by partial evaluation
- Customizable inductive type implementation in C
- Linearity checker for safe destructive update of values
- Downward-only closures
- Guaranteed tail recursion elimination

## Requiements

You need Coq and OCaml.

- Coq 8.16 (Coq 8.15 doesn't work)
- OCaml 4.14.0

You also need following to test codegen.

- ocamlfind 1.9.5
- ounit2 2.2.6 (ounit2 2.2.5 doesn't work)

## How to build, test and install

    make
    make check          # optional
    make install

## Interactive Examples

Codegen can be used interactively.
This is useful to examine C code generated from a Gallina function.

    Require Import codegen.codegen.

    Fixpoint add m n :=
      match m with
      | O => n
      | S m' => add m' (S n)
      end.

    CodeGen Gen add.
    (*
    nat
    add(nat v1_m, nat v2_n)
    {
      nat v3_m_;
      nat v4_n;
      entry_add:
      switch (sw_nat(v1_m))
      {
        default:
          return v2_n;
        case S_tag:
          v3_m_ = S_get_member_0(v1_m);
          v4_n = S(v2_n);
          v1_m = v3_m_;
          v2_n = v4_n;
          goto entry_add;
      }
    }
    *)

This code assumes `nat` type is defined in C.
Also, `sw_nat`, `S_tag`, `S_get_member_0` and `S` are should be defined in C.

We can define them as follows.
(Integer overflow is ignored here.)

    typedef nat uint64_t;
    #define sw_nat(n) ((n) == 0)
    #define S_tag 0
    #define S_get_member_0(n) ((n) - 1)
    #define S(n) ((n) + 1)

It is possible to configure code generation of inductive types.

    Require Import codegen.codegen.

    Fixpoint add m n :=
      match m with
      | O => n
      | S m' => add m' (S n)
      end.

    CodeGen InductiveType nat => "uint64_t".
    CodeGen InductiveMatch nat => ""
    | O => "case 0"
    | S => "default" "pred".
    CodeGen Constant O => "0".
    CodeGen Primitive S => "pred".

    CodeGen Gen add.
    (*
    uint64_t
    add(uint64_t v1_m, uint64_t v2_n)
    {
      uint64_t v3_m_;
      uint64_t v4_n;
      entry_add:
      switch (v1_m)
      {
        case 0:
          return v2_n;
        default:
          v3_m_ = pred(v1_m);
          v4_n = succ(v2_n);
          v1_m = v3_m_;
          v2_n = v4_n;
          goto entry_add;
      }
    }
    *)

We can use more simpler definition of nat type in C.

    #define pred(n) ((n) - 1)
    #define succ(n) ((n) + 1)

## Non-interactive Examples

Codegen can be used non-interactively.
This is useful as a part of a project.

power function:

    coqc -Q theories codegen -I src sample/pow.v # generates sample/pow_generated.c
    gcc -g -Wall sample/pow.c -o sample/pow
    sample/pow

rank algorithm of succinct data structure:

    coqc -Q theories codegen -I src sample/rank.v # generates sample/rank_generated.c
    gcc -g -Wall sample/rank.c -o sample/rank
    sample/rank rand
    sample/rank 11011110001010101111

sprintf function:

    coqc -Q theories codegen -I src sample/sprintf.v # generates sample/sprintf_generated.c
    gcc -g -Wall sample/sprintf.c -o sample/sprintf
    sample/sprintf

## Links

- Project Page https://github.com/akr/codegen
- Formatted development memo https://akr.github.io/codegen-doc/

## Authors

- Tanaka Akira
- Reynald Affeldt
- Jacques Garrigue

## Acknowledgment

This work is supported by JSPS KAKENHI Grant Number 15K12013 (2015-04-01 to 2018-03-31).

## Copyright

Copyright (C) 2016- National Institute of Advanced Industrial Science and Technology (AIST)
"monomorphization plugin for Coq"
AIST program registration number: H29PRO-2090

## License

GNU Lesser General Public License Version 2.1 or later
