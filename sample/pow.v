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

CodeGen IndType bool => "bool" swfunc "" with
| true => constant "true" case ""
| false => constant "false" case "0".

CodeGen SourceFile "sample/pow_generated.c".

CodeGen Snippet "prologue" "
#include <stdbool.h> /* for bool, true and false */
".

CodeGen IndType nat => "nat" swfunc "" with
| O => constant "0" case "0"
| S => primitive "nat_succ" case "" accessor "nat_pred".

CodeGen Snippet "prologue" "
#include <stdint.h>
typedef uint64_t nat;
#define nat_succ(n) ((n)+1)
#define nat_pred(n) ((n)-1)
".

CodeGen Primitive muln => "muln".
CodeGen Primitive odd => "odd".
CodeGen Primitive uphalf' => "uphalf".
CodeGen Snippet "prologue" "
#define muln(x,y) ((x) * (y))
#define odd(n) ((n)&1)

/* (n)+1 in uphalf(n) doesn't cause integer overflow
 * because uphalf' is applied to k' which is k-1.  */
#define uphalf(n) (((n)+1)>>1)
".

CodeGen Func fastpow_iter.
CodeGen Func fastpow.

CodeGen GenerateFile.
