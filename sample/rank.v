From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq ssrfun.
From mathcomp Require Import div prime.
Require Import codegen.codegen.

(* utility functions on nat *)
Definition neq0 n := n.-1.+1.
Definition bitlen n :=
  if n is 0 then 0 else (trunc_log 2 n).+1.

(* bits implementation *)
Inductive bits : Type := bseq of seq bool.
Definition seq_of_bits s := let: bseq l := s in l.
Coercion seq_of_bits : bits >-> list.
Definition bnil := bseq nil.
Definition bcons b (s : bits) := bseq (b :: s).
Definition bsize (s : bits) := size s.
Definition bnth (s : bits) i := nth false s i.
Definition bappend (s1 s2 : bits) := bseq (s1 ++ s2).
Definition bcount (b : bool) i l (s : bits) :=
  count_mem b (take l (drop i s)).

(* DArr implementation *)
(* w is used after monadification *)
Inductive DArr : Type := darr : nat -> seq nat -> DArr.
Definition bwidth D := let: darr w d := D in w.
Definition seq_of_D D := let: darr w d := D in d.
Definition emptyD w := darr w nil.
Definition pushD D v := let: darr w d := D in darr w (v :: d).
Definition lookupD D i :=
  let: darr w d := D in nth 0 d (size d - i.+1).
Definition sizeD D := let: darr w d := D in size d.

(* auxiliary data structure for rank *)
Record Aux : Set := mkAux {
  query_bit: bool;
  input_bits: bits;
  ratio: nat; (* number of small blocks in a large block *)
  blksz2: nat; (* number of bits in a small block *)
  dir1: DArr;
  dir2: DArr;
}.

Fixpoint buildDir2 b s sz2 c i D2 m2 :=
  if c is cp.+1 then
    let m := bcount b i sz2 s in
    buildDir2 b s sz2
      cp (i + sz2) (pushD D2 m2) (m2 + m)
  else
    (D2, m2).

Fixpoint buildDir1 b s k sz1 sz2 c i D1 D2 m1 :=
  if c is cp.+1 then
    let D1' := pushD D1 m1 in
    let (D2', m2) := buildDir2 b s sz2 k i D2 0 in
    buildDir1 b s k sz1 sz2
      cp (i + sz1) D1' D2' (m1 + m2)
  else
    (D1, D2, m1).

Definition buildDir b s k sz2 w1 w2 :=
  let sz1 := k * sz2 in
  let n := bsize s in
  let n2 := n %/ sz2 in (* number of small blocks *)
  let n1 := n2 %/ k in (* number of large blocks *)
  let: (D1, D2, m1) := buildDir1 b s k sz1 sz2
    n1 0 (emptyD w1) (emptyD w2) 0 in
  let (D2, m2) := buildDir2 b s sz2
    (n2 %% k) (n1 * sz1) D2 0 in
  (pushD D1 m1, pushD D2 m2).

Definition rank_init b s :=
  let n := bsize s in
  let kp := bitlen n in (* k - 1 *)
  let k := kp.+1 in  (* sz1 / sz2 *)
  let sz2p := bitlen n in (* sz2 - 1 *)
  let sz2 := sz2p.+1 in
  let sz1 := k * sz2 in
  let nn := n %/ sz2 in (* number of small blocks *)
  let w1 := neq0 (bitlen (n %/ sz1 * sz1)) in
  let w2 := neq0 (bitlen (kp * sz2)) in
  let (D1, D2) := buildDir b s k sz2 w1 w2 in
  mkAux b s k sz2 D1 D2.

Definition rank_lookup aux i :=
  let b := query_bit aux in
  let s := input_bits aux in
  let k := ratio aux in
  let sz2 := blksz2 aux in
  let D1 := dir1 aux in
  let D2 := dir2 aux in
  let j2 := i %/ sz2 in (* index in the 2nd-level dir *)
  let j3 := i %% sz2 in (* index in a small block *)
  let j1 := j2 %/ k in (* index in the 1st-level dir *)
  lookupD D1 j1 + lookupD D2 j2 +
  bcount b (j2 * sz2) j3 s.

Terminate Monomorphization addn.
Terminate Monomorphization subn.
Terminate Monomorphization muln.
Terminate Monomorphization divn.
Terminate Monomorphization modn.
Terminate Monomorphization bitlen.
Terminate Monomorphization bcount.
Terminate Monomorphization eqb.
Terminate Monomorphization negb.
Terminate Monomorphization eqn.
Monomorphization rank_init.
Monomorphization rank_lookup.

Print _buildDir2.
Print _buildDir1.
Print _buildDir.
Print _rank_init.
Print _rank_lookup.

CodeGen Linear DArr.
CodeGen LinearCheck _pred _neq0.
CodeGen LinearCheck _buildDir2.
CodeGen LinearCheck _buildDir1.
CodeGen LinearCheck _buildDir.
CodeGen LinearCheck _rank_init.
Fail CodeGen LinearCheck _rank_lookup.

GenCFile "rank_proved.c"
  _pred
  _neq0
  _buildDir2
  _buildDir1
  _buildDir
  _rank_init
  _rank_lookup.

