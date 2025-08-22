From mathcomp Require Import ssreflect ssrbool eqtype ssrfun ssrnat seq.
Require Import codegen.codegen.

CodeGen IndType bool => "bool" swfunc "" with
| true => constant "true" case ""
| false => constant "false" case "0".

CodeGen IndType nat => "nat" swfunc "" with
| O => constant "0" case "0"
| S => primitive "succn" case "" accessor "predn".

Definition succ2 n := S (S n).
CodeGen Func succ2.
CodeGen Gen "succ2".

Inductive TestType2 (A B : Type) := TestCons2 : A -> B -> TestType2 A B.
Definition non_mangled_code := TestCons2 bool nat.
CodeGen Func non_mangled_code => non_mangled_code_p non_mangled_code_s.
Print non_mangled_code_p.
Fail Print non_mangled_code_s.
CodeGen SimplifyFunction "non_mangled_code".
Print non_mangled_code_s.

CodeGen IndType bool*bool => "pair_bool_bool" with
| pair => primitive "make_pair_bool_bool" accessor "pair_bool_bool_fst" "pair_bool_bool_snd".

Definition swap {A B : Type} (p : A * B) := let (a, b) := p in (b, a).
Definition swap_bb p := @swap bool bool p.
CodeGen Func @swap bool bool => "swap" swap_p swap_s.
CodeGen Func swap_bb => swap_bb_p swap_bb_s.
CodeGen SimplifyFunction "swap_bb".
CodeGen SimplifyFunction "swap".
Print swap_bb_p.
Print swap_bb_s.
Print swap_p.
Print swap_s.
Goal swap = swap_bb_p. Proof. reflexivity. Qed.
Goal swap = swap_bb_s. Proof. reflexivity. Qed.
Goal swap_bb_p = swap_bb. Proof. reflexivity. Qed.
Goal swap_bb_s = swap_bb. Proof. reflexivity. Qed.
Print swap_p.
Print swap_s.
Print swap_bb_p.
Print swap_bb_s.

CodeGen Gen "swap" "swap_bb".
(*
static pair_bool_bool
swap(pair_bool_bool v1_p)
{
  bool v2_a;
  bool v3_b;
  v2_a = pair_bool_bool_fst(v1_p);
  v3_b = pair_bool_bool_snd(v1_p);
  return make_pair_bool_bool(v3_b, v2_a);
}

static pair_bool_bool
swap_bb(pair_bool_bool v1_p)
{
  return swap(v1_p);
}
*)

CodeGen Func negb.
CodeGen Gen "negb".
(*
static bool
negb(bool v1_b)
{
  switch (v1_b)
  {
    default:
      return false;
    case 0:
      return true;
  }
}
*)

Definition plus_1_2 := 1 + 2.
CodeGen Func plus_1_2.
CodeGen Gen "plus_1_2".

Definition foo1 := fun (x : nat) => x.
CodeGen Func foo1.
CodeGen Gen "foo1".

Definition foo2 := fun (x : nat) => let y := x in y.
CodeGen Func foo2.
CodeGen Gen "foo2".

Definition foo3 := fun (x : nat) => let y := x in y.
CodeGen Func foo3.
CodeGen Gen "foo3".

Definition foo4 := fun (x y : nat) => x + y.
CodeGen Func foo4.
CodeGen Gen "foo4".

Definition foo5 := fun (x y z : nat) => x + y + z.
CodeGen Func foo5.
CodeGen Gen "foo5".

Definition foo6 := fun (x : nat) => match x with O => x | S _ => x end.
CodeGen Func foo6.
CodeGen Gen "foo6".

Definition zero := 0.
Definition foo7 := zero.
CodeGen Func zero.
CodeGen Func foo7.
CodeGen Gen "zero".
CodeGen Gen "foo7".

Definition foo8 := fun (x : nat) => x + zero.
CodeGen Func foo8.
CodeGen Gen "foo8".

Definition foo9 := fun (x : nat) => match x with O => zero | S n => n + x end + x.
CodeGen Func foo9.
CodeGen Gen "foo9".

Section Sec1.
Variable a : nat.
Fixpoint foo10 b := a + b. (* non-recursive fixpoint *)
End Sec1.
Definition foo10' := foo10.
CodeGen Func foo10 => "foo10".
CodeGen Func foo10' => "foo10x".
Print CodeGen Specialization.
CodeGen Gen "foo10".

(* usual addition.  not tail recursion *)
Fixpoint add1 a b :=
  match a with
  | 0 => b
  | S n => S (add1 n b)
  end.
CodeGen Func add1.
CodeGen Gen "add1".

(* tail recursion which is translated into goto *)
Fixpoint add2 a b :=
  match a with
  | 0 => b
  | S n => add2 n (S b)
  end.
CodeGen Func add2.
CodeGen Gen "add2".

Section Sec2.
Variable a : nat.
Fixpoint add3 b :=
  match b with
  | 0 => a
  | S n => S (add3 n)
  end.
End Sec2.
CodeGen Func add3.
CodeGen Gen "add3".

(* needs tmp. variable to swap x and y at tail recursion *)
Fixpoint swapargtest (n x y : nat) :=
  match n with
  | 0 => x
  | S nn => swapargtest nn y x
  end.
CodeGen Func swapargtest.
CodeGen Gen "swapargtest".

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
CodeGen Func evenp.
CodeGen Gen "evenp".

(* generate beginning goto because the entry function is not beginning *)
CodeGen Func oddp.
CodeGen Gen "oddp".

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

CodeGen Func strange_pow2.
CodeGen Gen "strange_pow2".

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

CodeGen Func fib.
CodeGen Gen "fib".

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

CodeGen Func fib2.
CodeGen Gen "fib2".

(* artificial example.
  mftest and mftest3 has tail call.  mftest2 has non-tail call. *)
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
Compute mftest 5.
CodeGen Func mftest.
Print CodeGen Specialization.
CodeGen SimplifyFunction "mftest".
Print codegen_s27_mftest.
CodeGen Gen "mftest".

Fixpoint pow a k :=
  match k with
  | O => 1
  | S k' => a * pow a k'
  end.
CodeGen Func pow.
CodeGen Gen "pow".
(*
static nat
pow(nat v1_a, nat v2_k)
{
  nat v3_n;
  nat v4_k_;
  nat v5_n;
  switch (v2_k)
  {
    case 0:
      v3_n = 0;
      return succn(v3_n);
    default:
      v4_k_ = predn(v2_k);
      v5_n = pow(v1_a, v4_k_);
      return muln(v1_a, v5_n);
  }
}
*)

Definition TypeAlias := unit.
Definition f (x : TypeAlias) := x.
CodeGen Func f.
CodeGen SimplifyFunction "f".
Print codegen_s30_f.

Definition foo11 n := let ret := if n is 0 then 0 else 0 - n in ret.
CodeGen Func foo11.
CodeGen Gen "foo11".

