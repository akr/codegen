From mathcomp Require Import all_ssreflect.
Require Import String.
Require Import Ascii.

Open Scope string_scope. (* enable "string-literal" and str ++ str *)
Open Scope seq_scope. (* prefer seq ++ seq over str ++ str *)

Definition eqascii (a b : ascii) :=
  match ascii_dec a b with
  | left _ => true
  | right _ => false
  end.

Lemma eqasciiP : Equality.axiom eqascii.
Proof.
  move=> a b.
  rewrite /eqascii.
  case: (ascii_dec a b) => H.
    by apply ReflectT.
  by apply ReflectF.
Qed.

Canonical ascii_eqMixin := EqMixin eqasciiP.
Canonical ascii_eqType := Eval hnf in EqType ascii ascii_eqMixin.

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

Definition eqstr (a b : string) :=
  match string_dec a b with
  | left _ => true
  | right _ => false
  end.

(*Print Opaque Dependencies eqstr.*)

Lemma eqstrP : Equality.axiom eqstr.
Proof.
  move=> a b.
  rewrite /eqstr.
  case: (string_dec a b) => H.
    by apply ReflectT.
  by apply ReflectF.
Qed.

Canonical string_eqMixin := EqMixin eqstrP.
Canonical string_eqType := Eval hnf in EqType string string_eqMixin.

