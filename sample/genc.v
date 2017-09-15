From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat seq.
Require Import codegen.codegen.

Inductive TestType2 (A B : Type) := TestCons2 : A -> B -> TestType2 A B.
Definition non_mangled_code := TestCons2 bool nat.
Monomorphization non_mangled_code.
Print _non_mangled_code.

Definition swap {A B : Type} (p : A * B) := let (a, b) := p in (b, a).
Definition swap_bb p := @swap bool bool p.
Monomorphization swap_bb.
Print _swap_bb.
Print _swap_bool_bool.
Print _pair_bool_bool.
Goal swap = _swap_bool_bool. Proof. reflexivity. Qed.
Goal swap_bb = _swap_bb. Proof. reflexivity. Qed.

GenC _swap_bool_bool _swap_bb.

(*
#include <stdbool.h>
#define n0_true() true
#define n0_false() false
#define sw_bool(b) (b)
#define case_true_bool default
#define case_false_bool case false

#define prod_bool_bool int
#define field0_pair_prod_bool_bool(v) ((v) & 1)
#define field1_pair_prod_bool_bool(v) (((v) & 2) >> 1)
#define n2_pair_bool_bool(x, y) ((x) | ((y) << 1))

prod_bool_bool
n1_swap_bool_bool(prod_bool_bool v0_p)
{
  bool v1_a = field0_pair_prod_bool_bool(v0_p);
  bool v2_b = field1_pair_prod_bool_bool(v0_p);
  return n2_pair_bool_bool(v2_b, v1_a);
}
prod_bool_bool
n1_swap_bb(prod_bool_bool v3_p)
{
  return n1_swap_bool_bool(v3_p);
}

*)

Monomorphization negb.
Print _negb.
GenC _negb.

(*
bool
n1_negb(bool v4_b)
{
  switch (sw_bool(v4_b))
  {
    case_true_bool: { return n0_false(); }
    case_false_bool: { return n0_true(); }
  }
}
*)

(* Following examples needs "nat" type in C which can be implemented as follows.

#include <stdbool.h>
#define n0_true() true
#define n0_false() false

#define nat uint64_t
#define n0_O() ((nat)0)
#define n1_S(n) ((n)+1)
#define sw_nat(n) (n)
#define case_O_nat case 0
#define case_S_nat default
#define field0_S_nat(n) ((n)-1)

#define n2_add(a,b) ((a)+(b))
*)

Definition plus_1_2 := 1 + 2.
Monomorphization plus_1_2.
Print _plus_1_2.
GenC _plus_1_2.

Definition foo1 := fun (x : nat) => x.
Monomorphization foo1.
GenC _foo1.

Definition foo2 := fun (x : nat) => let y := x in y.
Monomorphization foo2.
GenC _foo2.

Definition foo3 := fun (x : nat) => let y := x in y.
Monomorphization foo3.
GenC _foo3.

Definition foo4 := fun (x y : nat) => x + y.
Monomorphization foo4.
GenC _foo4.

Definition foo5 := fun (x y z : nat) => x + y + z.
Monomorphization foo5.
GenC _foo5.

Definition foo6 := fun (x : nat) => match x with O => x | S _ => x end.
Monomorphization foo6.
GenC _foo6.

Definition zero := 0.
Definition foo7 := zero.
Monomorphization foo7.
GenC _zero.
GenC _foo7.

Definition foo8 := fun (x : nat) => x + zero.
Monomorphization foo8.
Print _foo8.
GenC _foo8.

Definition foo9 := fun (x : nat) => match x with O => zero | S n => n + x end + x.
Monomorphization foo9.
GenC _foo9.

(*
Section Sec1.
Variable a : nat.
Fixpoint foo10 b := a + b.
End Sec1.
Definition foo10' := foo10.
Monomorphization foo10'.
Print _foo10.
GenC _foo10.
*)

(* usual addition.  not tail recursion *)
Fixpoint add1 a b :=
  match a with
  | 0 => b
  | S n => S (add1 n b)
  end.
Monomorphization add1.
Print _add1.
GenC _add1.

(* tail recursion which is translated into goto *)
Fixpoint add2 a b :=
  match a with
  | 0 => b
  | S n => add2 n (S b)
  end.
Monomorphization add2.
Print _add2.
GenC _add2.

(* argument outside of fix is supported *)
(*
Section Sec2.
Variable a : nat.
Fixpoint add3 b :=
  match b with
  | 0 => a
  | S n => S (add3 n)
  end.
End Sec2.
Monomorphization add3.
Print _add3.
GenC _add3.
*)

(* needs tmp. variable to swap x and y at tail recursion *)
Fixpoint swapargtest (n x y : nat) :=
  match n with
  | 0 => x
  | S nn => swapargtest nn y x
  end.
Monomorphization swapargtest.
Print _swapargtest.
GenC _swapargtest.

(* mutual recursion.  only tail calls *)
Fixpoint evenp n :=
  match n with
  | 0 => true
  | S nn => oddp nn
  end
with oddp n :=
  match n with
  | 0 => false
  | S nn => evenp nn
  end.

Compute evenp 0.
Compute evenp 1.
Compute evenp 2.
Compute oddp 0.
Compute oddp 1.
Compute oddp 2.

(* beginning goto not required because the entry function is beginning *)
Monomorphization evenp.
Print _evenp.
GenC _evenp.

(* generate beginning goto because the entry function is not beginning *)
Monomorphization oddp.
Print _oddp.
GenC _oddp.

(* strange_pow2 n m = 2 ^ n + m *)
(* This recursive function contains tail call and non-tail call *)
Fixpoint strange_pow2 n m :=
  match n with
  | O => S m
  | S nn => strange_pow2 nn (strange_pow2 nn m) (* tail call and non-tail call *)
  end.

Goal forall n m, strange_pow2 n m = 2 ^ n + m.
Proof.
  elim; first by [].
  move=> n IH m /=.
  by rewrite IH IH addnA expnS mul2n -addnn.
Qed.

Compute strange_pow2 0 0.
Compute strange_pow2 1 0.
Compute strange_pow2 2 0.
Compute strange_pow2 3 0.
Compute strange_pow2 4 0.

Monomorphization strange_pow2.
Print _strange_pow2.
GenC _strange_pow2.

(* Two non-tail call.  No tail call. *)
Fixpoint fib n :=
  match n with
  | O => 0
  | S O => 1
  | S ((S n2) as n1) => fib n2 + fib n1
  end.

Compute fib 0.
Compute fib 1.
Compute fib 2.
Compute fib 3.
Compute fib 4.
Compute fib 5.
Compute fib 6.
Compute fib 7.

Monomorphization fib.
Print _fib.
GenC _fib.

(* mutually recursive.  tail call and non-tail call *)
Fixpoint fib2 n :=
  match n with
  | O => 0
  | S nn => fib2S nn (* tail call *)
  end
with fib2S n :=
  match n with
  | O => 1
  | S nn => fib2 nn + fib2S nn (* non-tail calls *)
  end.

Compute fib2 0.
Compute fib2 1.
Compute fib2 2.
Compute fib2 3.
Compute fib2 4.
Compute fib2 5.
Compute fib2 6.
Compute fib2 7.

Monomorphization fib2.
Print _fib2.
GenC _fib2.

(* artificial example.
  mftest and mftest3 has non-tail call.  mftest2 has only tail call. *)
Fixpoint mftest (n : nat) :=
  match n with
  | O => O
  | S nn => mftest2 nn
  end
with mftest2 n :=
  match n with
  | O => O
  | S nn => mftest3 nn + 1
  end
with mftest3 n :=
  match n with
  | O => O
  | S nn => mftest nn
  end.

Monomorphization mftest.
Print _mftest.
GenC _mftest.

Fixpoint pow a k :=
  match k with
  | O => 1
  | S k' => a * pow a k'
  end.
Monomorphization pow.
GenC _pow.
(*
nat
n2_pow(nat v88_a, nat v87_k)
{
  switch (sw_nat(v87_k))
  {
    case_O_nat: { nat v90_n = n0_O(); return n1_S(v90_n); }
    case_S_nat: {
      nat v91_k_ = field0_S_nat(v87_k);
      nat v92_n = n2_pow(v88_a, v91_k_);
      return n2_muln(v88_a, v92_n);
    }
  }
}
*)

Definition TypeAlias := unit.
Definition f (x : TypeAlias) := x.
Monomorphization f.

