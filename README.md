# monomorphization plugin for Coq

This software provides Coq commands to monomorphize Gallina definitions and
then generate C source code.

## Home page

https://github.com/akr/monomorphization

## Requiements

- Coq 8.6 (Coq 8.5 doesn't work)

## How to build

    make

## How to run

    coqide -I src -Q theories Monomorph sample/pow.v

## How to use

See sample/ directory.

## Authors

- Tanaka Akira
- Reynald Affeldt
- Jacques Garrigue

## Acknowledgment

This work is supported by JSPS KAKENHI Grant Number 15K12013.

## Copyright

Copyright (C) 2016- National Institute of Advanced Industrial Science and Technology (AIST)
"monomorphization plugin for Coq"
AIST program registration number: H29PRO-2090

## License

GNU Lesser General Public License Version 2.1 or later
