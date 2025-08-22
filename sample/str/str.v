From mathcomp Require Import all_ssreflect.
From HB Require Import structures.

Require Import nat.
Require Import ascii.
From Stdlib Require Ascii.
From Stdlib Require Import String.
(*
Inductive string : Set :=
| EmptyString : string
| String : ascii -> string -> string.
*)

Open Scope string_scope. (* enable "string-literal" and str ++ str *)
Open Scope seq_scope. (* prefer seq ++ seq over str ++ str *)

Fixpoint seq_of_str str :=
  match str with
  | "" => nil
  | String c str' => c :: (seq_of_str str')
  end.

Fixpoint str_of_seq s :=
  match s with
  | nil => ""
  | c :: s' => String c (str_of_seq s')
  end.

Lemma str_of_seq_of_str str : str_of_seq (seq_of_str str) = str.
Proof. by elim: str => [|c str /= ->]. Qed.

Lemma seq_of_str_of_seq s : seq_of_str (str_of_seq s) = s.
Proof. by elim: s => [|c s /= ->]. Qed.

Coercion seq_of_str : string >-> seq.

Definition eqstr a b := seq_of_str a == seq_of_str b.

Lemma eqstr_eq a b : (eqstr (str_of_seq a) (str_of_seq b)) = (a == b).
Proof. by rewrite /eqstr 2!seq_of_str_of_seq. Qed.

Lemma eqstrP : Equality.axiom eqstr.
Proof.
  move=> a' b'.
  rewrite -(str_of_seq_of_str a') -(str_of_seq_of_str b').
  move: (seq_of_str a') (seq_of_str b') => a b.
  clear a' b'.
  rewrite eqstr_eq.
  apply: (iffP idP).
    by move=> /eqP ->.
  rewrite -{2}(seq_of_str_of_seq a) => ->.
  by rewrite seq_of_str_of_seq.
Qed.

HB.instance Definition _ := hasDecEq.Build string eqstrP.

Definition nthstr (s : string) (i : nat) : Ascii.ascii :=
  nth Ascii.zero (seq_of_str s) i.

Definition takestr (n : nat) (s : string) : string :=
  str_of_seq (take n (seq_of_str s)).

Definition dropstr (n : nat) (s : string) : string :=
  str_of_seq (drop n (seq_of_str s)).

Definition takestrr (n : nat) (s : string) : string :=
  str_of_seq (drop (size s - n) (seq_of_str s)).

Definition dropstrr (n : nat) (s : string) : string :=
  str_of_seq (take (size s - n) (seq_of_str s)).
