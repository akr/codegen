From mathcomp Require Import all_ssreflect.

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

CodeGen Inductive Type bool => "bool".
CodeGen Inductive Match bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

CodeGen Source File "sample/pow_generated.c".

CodeGen Snippet "
#include <stdbool.h> /* for bool, true and false */
".

CodeGen Inductive Type nat => "nat".
CodeGen Inductive Match nat => ""
| O => "case 0"
| S => "default" "nat_pred".
CodeGen Constant O => "0".
CodeGen Primitive S => "nat_succ".

CodeGen Snippet "
#include <stdint.h>
typedef uint64_t nat;
#define nat_succ(n) ((n)+1)
#define nat_pred(n) ((n)-1)
".

CodeGen Primitive muln => "muln".
CodeGen Primitive odd => "odd".
CodeGen Primitive uphalf' => "uphalf".
CodeGen Snippet "
#define muln(x,y) ((x) * (y))
#define odd(n) ((n)&1)

/* (n)+1 in uphalf(n) doesn't cause integer overflow
 * because uphalf' is applied to k' which is k-1.  */
#define uphalf(n) (((n)+1)>>1)
".

CodeGen Static Function fastpow_iter.
CodeGen Static Function fastpow.

CodeGen GenerateFile.
