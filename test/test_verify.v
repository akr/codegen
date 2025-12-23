From Ltac2 Require Import Ltac2.
From codegen Require Import codegen.
From codegen Require Import verify.

Goal forall a b,
  (fix add a b :=
    match a with
    | O => b
    | S a' => S (add a' b)
    end) a b =
  (fix add a b :=
    match a with
    | O => fun c => c
    | S a' => fun c => S (add a' c)
    end b) a b.
Proof.
  intros.
  codegen_solve.
Qed.

Definition merge1 :=
  fix f (s1 : list nat) :=
    fix g (s2 : list nat) :=
      match s1 with
      | nil => s2
      | cons x1 s1' =>
          match s2 with
          | nil => s1
          | cons x2 s2' =>
              if Nat.leb x1 x2 then
                cons x1 (f s1' s2)
              else
                cons x2 (g s2')
          end
      end.

Definition merge2 :=
  fix f (s1 : list nat) :=
    fix g (s2 : list nat) :=
      match s1 with
      | nil => s2
      | cons x1 s1' =>
          match s2 with
          | nil => fun _ => s1
          | cons x2 s2' => fun _ =>
              if Nat.leb x1 x2 then
                cons x1 (f s1' s2)
              else
                cons x2 (g s2')
          end tt
      end.

Goal forall s1 s2, merge1 s1 s2 = merge2 s1 s2.
Proof.
  intros.
  unfold merge1, merge2.
  codegen_fix.
  intros.
  codegen_fix.
  intros.
  codegen_matchapp.
    reflexivity.
  intros.
  codegen_matchapp.
    reflexivity.
  intros.
  codegen_matchapp.
    codegen_apparg.
      codegen_applyhyp.
    reflexivity.
  codegen_apparg.
    codegen_applyhyp.
  reflexivity.
Qed.

Goal forall s1 s2, merge1 s1 s2 = merge2 s1 s2.
Proof.
  intros.
  unfold merge1, merge2.
  codegen_solve.
Qed.

Definition add1 :=
  fix f (a b : nat) : nat :=
    match a with
    | O => b
    | S a' => S (f a' b)
    end.

Definition add2 :=
  fix f (a : nat) : nat -> nat :=
    match a with
    | O => fun b => b
    | S a' => fun b => S (f a' b)
    end.

Goal forall a b, add1 a b = add2 a b.
Proof.
  intros.
  unfold add1, add2.
  codegen_fix.
  intros.
  codegen_matchapp.
    reflexivity.
  intros.
  codegen_apparg.
    codegen_applyhyp.
  reflexivity.
Qed.

Goal forall a b, add1 a b = add2 a b.
Proof.
  unfold add1, add2.
  codegen_solve.
Qed.

Definition sub1 :=
  fix f (a b : nat) : nat :=
    match a with
    | O => O
    | S a' =>
        match b with
        | O => a
        | S b' => f a' b'
        end
    end.

Definition sub2 :=
  fix f (a b : nat) : nat :=
    match a with
    | O => O
    | S a' =>
        match b with
        | O => fun a' => a
        | S b' => fun a' => f a' b'
        end a'
    end.

Goal forall a b, sub1 a b = sub2 a b.
Proof.
  intros.
  unfold sub1, sub2.
  codegen_solve.
Qed.

Definition mem_seq1 :=
  fix mem_seq (s : list nat) (x : nat) :=
  match s with
  | nil => (fun z => false)
  | cons y s' => (fun z => orb (Nat.eqb y z) (mem_seq s' z))
  end x.

Definition mem_seq2 :=
  fix mem_seq (s : list nat) (x : nat) :=
  match s with
  | nil => false
  | cons y s' => orb (Nat.eqb y x) (mem_seq s' x)
  end.

Goal forall s x, mem_seq1 s x = mem_seq2 s x.
Proof.
  intros.
  unfold mem_seq1, mem_seq2.
  codegen_solve.
Qed.

Definition fib1 :=
fix fib (n : nat) : nat :=
  match n with
  | O => 0
  | S n1 =>
      match n1 with
      | O => 1
      | S n2 => fib n1 + fib n2
      end
  end.

Definition fib2 :=
fix fib (n : nat) : nat :=
  match n with
  | O => 0
  | S n1 =>
      match n1 with
      | O => fun _ => 1
      | S n2 => fun _ => fib n1 + fib n2
      end tt
  end.

Goal forall n, fib1 n = fib2 n.
Proof.
  intros.
  unfold fib1, fib2.
  codegen_solve.
Qed.

Definition even1 :=
fix even n :=
  match n with
  | O => true
  | S n' => odd n'
  end
with odd n :=
  match n with
  | O => false
  | S n' => even n'
  end
for even.

Definition even2 :=
fix even n :=
  match n with
  | O => fun _ => true
  | S n' => fun _ => odd n'
  end tt
with odd n :=
  match n with
  | O => false
  | S n' => even n'
  end
for even.

Goal forall n, even1 n = even2 n.
Proof.
  intros.
  unfold even1, even2.
  codegen_solve.
Qed.

Definition half1 :=
fix half n :=
  match n with
  | O => O
  | S n' => half' n'
  end
with half' n :=
  match n with
  | O => O
  | S n' => S (half n')
  end
for half.

Definition half2 :=
fix half n :=
  match n with
  | O => O
  | S n' => half' n'
  end
with half' n :=
  match n with
  | O => fun _ => O
  | S n' => fun _ => S (half n')
  end tt
for half.

Goal forall n, half1 n = half2 n.
Proof.
  intros.
  unfold half1, half2.
  codegen_solve.
Qed.

Definition odd1' :=
fix odd' n :=
  match n with
  | O => false
  | S O => true
  | S (S n') => odd' n'
  end.

Definition odd2' :=
fix odd' n :=
  match n with
  | O => fun _ => false
  | S O => fun _ => true
  | S (S n') => fun _ => odd' n'
  end tt.

Goal forall n, odd1' n = odd2' n.
Proof.
  intros.
  unfold odd1', odd2'.
  codegen_solve.
Qed.

Definition ack1 :=
  fix f m :=
    fix g n :=
      match m with
      | O => n + 1
      | S m' =>
          match n with
          | O => f m' 1
          | S n' => f m' (g n')
          end
      end.

Definition ack2 :=
  fix f m :=
    fix g n :=
      match m with
      | O => n + 1
      | S m' =>
          match n with
          | O => fun _ => f m' 1
          | S n' => fun _ => f m' (g n')
          end tt
      end.

Goal forall m n, ack1 m n = ack2 m n.
Proof.
  intros.
  unfold ack1, ack2.
  codegen_solve.
Qed.

(* https://en.wikipedia.org/wiki/Sudan_function *)
Definition sudan1 :=
  fix f n x :=
    fix g y :=
      match n with
      | O => x + y
      | S n' =>
          match y with
          | O => x
          | S y' => f n' (g y') (g y' + y' + 1)
          end
      end.

Definition sudan2 :=
  fix f n x :=
    fix g y :=
      match n with
      | O => x + y
      | S n' =>
          match y with
          | O => fun _ => x
          | S y' => fun _ => f n' (g y') (g y' + y' + 1)
          end tt
      end.

Goal forall n x y, sudan1 n x y = sudan2 n x y.
Proof.
  intros.
  unfold sudan1, sudan2.
  codegen_solve.
Qed.

Section forest.
Variable A B : Set.
Inductive tree : Set := node : A -> forest -> tree
with forest : Set :=
| leaf : B -> forest
| cons : tree -> forest -> forest.

Definition size_tree1 :=
fix size_tree t :=
  match t with
  | node _ f => 1 + (size_forest f)
  end
with size_forest f :=
  match f with
  | leaf _ => 1
  | cons t f' => size_tree t + size_forest f'
  end
for size_tree.

Definition size_tree2 :=
fix size_tree t :=
  match t with
  | node _ f => fun _ => 1 + (size_forest f)
  end tt
with size_forest f :=
  match f with
  | leaf _ => fun _ => 1
  | cons t f' => fun _ => size_tree t + size_forest f'
  end tt
for size_tree.

Goal forall t, size_tree1 t = size_tree2 t.
Proof.
  intros.
  unfold size_tree1, size_tree2.
  codegen_solve.
Qed.
End forest.

Definition gcd1 :=
  fix f m :=
    fix g n :=
      match m with
      | O => n
      | S m' =>
          match n with
          | O => m
          | S n' =>
              if Nat.leb m' n' then
                g (n' - m')
              else
                f (m' - n') n
          end
      end.

Definition gcd2 :=
  fix f m :=
    fix g n :=
      match m with
      | O => n
      | S m' =>
          match n with
          | O => fun _ => m
          | S n' => fun _ =>
              if Nat.leb m' n' then
                g (n' - m')
              else
                f (m' - n') n
          end tt
      end.

Goal forall m n, gcd1 m n = gcd2 m n.
Proof.
  intros.
  unfold gcd1, gcd2.
  codegen_solve.
Qed.

Definition div1 n d :=
  match d with
  | O => 0
  | S d' =>
      let fix f n :=
        match n - d' with
        | O => 0
        | S n'' => S (f n'')
        end
      in f n
  end.

Definition div2 n d :=
  match d with
  | O => 0
  | S d' =>
      let fix f n :=
        match n - d' with
        | O => fun _ => 0
        | S n'' => fun _ => S (f n'')
        end tt
      in f n
  end.

(* Rocq 9.0.0 works, but Rocq 9.1.0 don't.
  https://github.com/rocq-prover/rocq/issues/21452 *)
(*
Goal forall n d, div1 n d = div2 n d.
Proof.
  intros.
  cbv beta delta [div1 div2].
  codegen_solve.
Qed.
*)

Definition mod1 n d :=
  match d with
  | O => n
  | S d' =>
      let fix f n :=
        match n - d' with
        | O => n
        | S n'' => f n''
        end
      in f n
  end.

Definition mod2 n d :=
  match d with
  | O => fun _ => n
  | S d' => fun _ =>
      let fix f n :=
        match n - d' with
        | O => n
        | S n'' => f n''
        end
      in f n
  end tt.

Goal forall n d, mod1 n d = mod2 n d.
Proof.
  intros.
  cbv beta delta [mod1 mod2].
  codegen_solve.
Qed.
