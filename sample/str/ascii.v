From mathcomp Require Import all_ssreflect.
From HB Require Import structures.

Require Import Ascii.
(*
Inductive ascii : Set :=
  Ascii : (*LSB*)bool -> bool -> bool -> bool ->
          bool -> bool -> bool -> (*MSB*)bool -> ascii.
*)


Open Scope string_scope. (* enable "string-literal" and str ++ str *)
Open Scope seq_scope. (* prefer seq ++ seq over str ++ str *)

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

