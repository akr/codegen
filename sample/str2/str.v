From mathcomp Require Import all_ssreflect.
From HB Require Import structures.

Require Ascii.
Require Import ascii.

Require Import String.
(*
Inductive string : Set :=
| EmptyString : string
| String : ascii -> string -> string.
*)

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

Definition eqstr (a b : string) := ((seq_of_str a) == (seq_of_str b)).

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

(* codegen-dependent part *)

Require Import codegen.codegen.
Require Import nat.
Require Import ascii.

(* C-level API configurations *)

CodeGen IndType string => "str_t" swfunc "str_sw" with
| EmptyString => primitive "str_empty" case "0"
| String => nofunc case "" accessor "str_head" "str_tail".

CodeGen Primitive eqstr => "eqstr".
CodeGen Primitive nthstr => "nthstr".
CodeGen Primitive takestr => "takestr".
CodeGen Primitive dropstr => "dropstr".
CodeGen Primitive takestrr => "takestrr".
CodeGen Primitive dropstrr => "dropstrr".

(* C code generation part *)

CodeGen HeaderFile "str.h".
CodeGen SourceFile "str.c".

CodeGen HeaderSnippet "prologue" "
#ifndef STR_H
#define STR_H
#include <stdbool.h>
#include <string.h>
#include ""nat.h""
#include ""ascii.h""
".

CodeGen HeaderSnippet "type_impls" "
typedef struct {
  uint8_t *ptr;
  uint64_t size;
} str_t;
#define str_sw(x) ((x).size)
#define str_head(x) (*(x).ptr)
static inline str_t str_tail(str_t x) { return (str_t){ x.ptr+1, x.size-1 }; }
#define str_empty() ((str_t){ (uint8_t *)0, 0 })
static inline bool eqstr(str_t x, str_t y) { return x.size == y.size && memcmp(x.ptr, y.ptr, x.size) == 0; }
static inline uint8_t nthstr(str_t s, nat i) { return s.size <= i ? 0 : s.ptr[i]; }
static inline str_t takestr(nat n, str_t s) { if (s.size < n) n = s.size; return (str_t){ s.ptr, n }; }
static inline str_t dropstr(nat n, str_t s) { if (s.size < n) n = s.size; return (str_t){ s.ptr+n, s.size-n }; }
static inline str_t takestrr(nat n, str_t s) { if (s.size < n) n = s.size; return (str_t){ s.ptr+(s.size-n), n }; }
static inline str_t dropstrr(nat n, str_t s) { if (s.size < n) n = s.size; return (str_t){ s.ptr, s.size-n }; }
".

CodeGen Snippet "prologue" "#include ""str.h""".

Fixpoint mystrlen (x : string) : nat :=
  match x with
  | EmptyString => 0
  | String _ t => S (mystrlen t)
  end.

CodeGen Func mystrlen.

CodeGen HeaderSnippet "epilogue" "#endif /* STR_H */".

CodeGen GenerateFile.
