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

(* nat array implementation for directories
  MDArr is mutable array used for building phase
  DArr is immutable array used for lookup phase
  The elements must be lower than 2^w.
  This restriction is proved using monadification *)
Inductive MDArr : Type := mdarr : nat -> seq nat -> MDArr.
Definition bwidth D := let: mdarr w d := D in w.
Definition seq_of_MD D := let: mdarr w d := D in d.
Definition emptyD w := mdarr w nil.
Definition pushD D v := let: mdarr w d := D in mdarr w (v :: d).

Inductive DArr : Type := darr : nat -> seq nat -> DArr.
Definition freezeD D := let: mdarr w d := D in darr w d.
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
  mkAux b s k sz2 (freezeD D1) (freezeD D2).

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

CodeGen HeaderFile "sample/rank_generated.h".
CodeGen SourceFile "sample/rank_generated.c".

CodeGen Linear MDArr.

CodeGen IndType bool => "bool" swfunc "" with
| true => constant "true" case ""
| false => constant "false" case "0".

CodeGen IndType nat => "nat" swfunc "" with
| O => constant "0" case "0"
| S => primitive "succn" case "" accessor "predn".
CodeGen Primitive addn => "addn".
CodeGen Primitive subn => "subn".
CodeGen Primitive muln => "muln".
CodeGen Primitive divn => "divn".
CodeGen Primitive modn => "modn".
CodeGen Primitive bitlen => "bitlen".
CodeGen Primitive bcount => "bcount".
CodeGen Primitive eqb => "eqb".
CodeGen Primitive negb => "negb".
CodeGen Primitive eqn => "eqn".

CodeGen IndType bits => "bits".
CodeGen IndType DArr => "DArr".
CodeGen IndType MDArr => "MDArr" with
| mdarr => deallocator "dealloc_MDArr".

CodeGen IndType MDArr*MDArr => "pair_MDArr_MDArr" with
| pair => primitive "make_pair_MDArr_MDArr" accessor "pair_MDArr_MDArr_D1" "pair_MDArr_MDArr_D2".
CodeGen IndImp MDArr*MDArr.

CodeGen IndType MDArr*nat => "pair_MDArr_nat" with
| pair => primitive "make_pair_MDArr_nat" accessor "pair_MDArr_nat_D" "pair_MDArr_nat_n".
CodeGen IndImp MDArr*nat.

CodeGen IndType MDArr*MDArr*nat => "pair_2MDArr_nat" with
| pair => primitive "make_pair_2MDArr_nat" accessor "pair_2MDArr_nat_D12" "pair_2MDArr_nat_n".
CodeGen IndImp MDArr*MDArr*nat.

CodeGen IndType Aux => "Aux" with
| mkAux =>
  primitive "mkAux"
  accessor
    "aux_query_bit" "aux_input_bits" "aux_blksz2"
    "aux_ratio" "aux_dir1" "aux_dir2".
CodeGen Primitive query_bit => "aux_query_bit".
CodeGen Primitive input_bits => "aux_input_bits".
CodeGen Primitive blksz2 => "aux_blksz2".
CodeGen Primitive ratio => "aux_ratio".
CodeGen Primitive dir1 => "aux_dir1".
CodeGen Primitive dir2 => "aux_dir2".
CodeGen IndImp Aux where heap on.

CodeGen Primitive bsize.
CodeGen Primitive freezeD.
CodeGen Primitive emptyD.
CodeGen Primitive pushD.
CodeGen Primitive lookupD.

(*
CodeGen Func Nat.pred.
CodeGen Func neq0.
CodeGen Func buildDir2.
CodeGen Func buildDir1.
CodeGen Func buildDir.
*)

CodeGen Func rank_init.
CodeGen Func rank_lookup.

CodeGen ResolveDependencies.
(*Print CodeGen Generation List.*)
CodeGen GenerateFile.

(* GenCFile checks them internaly
CodeGen LinearCheck _pred _neq0.
CodeGen LinearCheck _buildDir2.
CodeGen LinearCheck _buildDir1.
CodeGen LinearCheck _buildDir.
CodeGen LinearCheck _rank_init.
CodeGen LinearCheck _rank_lookup.
*)

(*
CodeGen GenCFile "sample/rank_generated.c"
  _pred
  _neq0
  _buildDir2
  _buildDir1
  _buildDir
  _rank_init
  _rank_lookup.

*)
