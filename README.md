# codegen plugin for Coq

This software provides Coq commands to generate C source code
from Gallina definitions.

## Home page

https://github.com/akr/codegen

## Requiements

You need Coq and OCaml.

- Coq 8.12 (Coq 8.11 doesn't work)
- OCaml 4.10.0

You also need following to test codegen.

- ocamlfind 1.8.1
- ounit2 2.2.1

## How to build, test and install

    make
    make check          # optional
    make install

## Examples

power function:

    coqc sample/pow.v # generates sample/pow_proved.c
    gcc -g -Wall sample/pow.c -o sample/pow
    sample/pow

rank algorithm of succinct data structure:

    coqc sample/rank.v # generates sample/rank_proved.c
    gcc -g -Wall sample/rank.c -o sample/rank
    sample/rank rand

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
