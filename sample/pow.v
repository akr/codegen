From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat.

Require Import codegen.codegen.

Definition uphalf' n := n - n./2.

Lemma uphalf'_uphalf n : uphalf' n = uphalf n.
Proof.
  rewrite /uphalf' -{1}[n]odd_double_half.
  by rewrite -addnn addnA addnK uphalf_half.
Qed.

(* (uphalf' k') is used instead of (k./2) for decreasing argument detection *)
Fixpoint fastpow_iter a k x :=
  if k is k'.+1 then
    if odd k then
      fastpow_iter a k' (a * x)
    else
      fastpow_iter (a * a) (uphalf' k') x
  else
    x.

Definition fastpow a k := fastpow_iter a k 1.

Terminate Monomorphization odd.
Terminate Monomorphization muln.
Terminate Monomorphization uphalf.
Monomorphization fastpow.
Print _fastpow.
Print _fastpow_iter.

GenCFile "pow_proved.c" _fastpow_iter _fastpow.
