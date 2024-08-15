Require Import codegen.codegen.

Require Import Ascii.
Require Import ascii.
(*
Inductive ascii : Set :=
  Ascii : (*LSB*)bool -> bool -> bool -> bool ->
          bool -> bool -> bool -> (*MSB*)bool -> ascii.
*)

CodeGen InductiveType ascii => "uint8_t".
CodeGen InductiveMatch ascii => "" with
| Ascii => "" "ascii_bit0" "ascii_bit1" "ascii_bit2" "ascii_bit3"
              "ascii_bit4" "ascii_bit5" "ascii_bit6" "ascii_bit7".
CodeGen Primitive Ascii => "ascii_cstr".

CodeGen Primitive eqascii => "eqascii".
