From mathcomp Require Import all_ssreflect.
From HB Require Import structures.

From Stdlib Require Import Ascii.
(*
Inductive ascii : Set :=
  Ascii : (*LSB*)bool -> bool -> bool -> bool ->
          bool -> bool -> bool -> (*MSB*)bool -> ascii.
*)

Definition eqascii a b :=
  let: Ascii a1 a2 a3 a4 a5 a6 a7 a8 := a in
  let: Ascii b1 b2 b3 b4 b5 b6 b7 b8 := b in
  (a1 == b1) && (a2 == b2) && (a3 == b3) && (a4 == b4) &&
  (a5 == b5) && (a6 == b6) && (a7 == b7) && (a8 == b8).

Lemma eqasciiP : Equality.axiom eqascii.
Proof.
  move=> a b.
  apply: (iffP idP).
    case: a => a1 a2 a3 a4 a5 a6 a7 a8.
    case: b => b1 b2 b3 b4 b5 b6 b7 b8.
    rewrite /eqascii.
    do 7 rewrite andbC => /andP [] /eqP ->.
    by move=> /eqP ->.
  move=> ->.
  case: b => b1 b2 b3 b4 b5 b6 b7 b8 /=.
  by do 8 rewrite eq_refl.
Qed.

HB.instance Definition _ := hasDecEq.Build ascii eqasciiP.

(* codegen-dependent part *)

Require Import codegen.codegen.

(* C-level API configurations *)

CodeGen IndType ascii => "uint8_t" with
| Ascii => primitive "ascii_cstr"
           accessor "ascii_bit0" "ascii_bit1" "ascii_bit2" "ascii_bit3"
                    "ascii_bit4" "ascii_bit5" "ascii_bit6" "ascii_bit7".

CodeGen Primitive eqascii => "eqascii".

(* C code generation part *)

CodeGen HeaderFile "ascii.h".
CodeGen SourceFile "ascii.c".

CodeGen HeaderSnippet "prologue" "
#ifndef ASCII_H
#define ASCII_H
#include <stdint.h>
".

CodeGen HeaderSnippet "func_impls" "
#define ascii_bit0(a) (((a) & 0x01) != 0)
#define ascii_bit1(a) (((a) & 0x02) != 0)
#define ascii_bit2(a) (((a) & 0x04) != 0)
#define ascii_bit3(a) (((a) & 0x08) != 0)
#define ascii_bit4(a) (((a) & 0x10) != 0)
#define ascii_bit5(a) (((a) & 0x20) != 0)
#define ascii_bit6(a) (((a) & 0x40) != 0)
#define ascii_bit7(a) (((a) & 0x80) != 0)
#define ascii_cstr(b0, b1, b2, b3, b4, b5, b6, b7) \
  (((b0)     ) | ((b1) << 1) | ((b2) << 2) | ((b3) << 3) | \
   ((b4) << 4) | ((b5) << 5) | ((b6) << 6) | ((b7) << 7))
#define eqascii(a, b) ((a) == (b))
".

CodeGen Snippet "prologue" "#include ""ascii.h""".

CodeGen HeaderSnippet "epilogue" "#endif /* ASCII_H */".
CodeGen GenerateFile.
