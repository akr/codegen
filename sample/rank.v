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

CodeGen Linear MDArr.

CodeGen Inductive Type bool => "bool".
CodeGen Inductive Match bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

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
CodeGen Snippet "
#define addn(x,y) ((x) + (y))
#define subn(x,y) ((x) - (y))
#define muln(x,y) ((x) * (y))
#define divn(x,y) ((x) / (y))
#define modn(x,y) ((x) % (y))
".

CodeGen Inductive Type bits => "bits".
CodeGen Inductive Type DArr => "DArr".
CodeGen Inductive Type MDArr => "MDArr".

CodeGen Inductive Type (MDArr * MDArr)%type => "prod_MDArr_MDArr".
CodeGen Inductive Match (MDArr * MDArr)%type => ""
| pair => "" "field0_pair_prod_MDArr_MDArr" "field1_pair_prod_MDArr_MDArr".
CodeGen Primitive pair MDArr MDArr => "pair_MDArr_MDArr".
CodeGen Snippet "
typedef struct {
  MDArr D1;
  MDArr D2;
} prod_MDArr_MDArr;
#define pair_MDArr_MDArr(D1, D2) ((prod_MDArr_MDArr){ (D1), (D2) })
#define field0_pair_prod_MDArr_MDArr(x) ((x).D1)
#define field1_pair_prod_MDArr_MDArr(x) ((x).D2)
".

CodeGen Inductive Type (MDArr * nat)%type => "prod_MDArr_nat".
CodeGen Inductive Match (MDArr * nat)%type => ""
| pair => "" "field0_pair_prod_MDArr_nat" "field1_pair_prod_MDArr_nat".
CodeGen Primitive pair MDArr nat => "pair_MDArr_nat".
CodeGen Snippet "
typedef struct {
  MDArr D;
  nat n;
} prod_MDArr_nat;
#define pair_MDArr_nat(D, n) ((prod_MDArr_nat){ (D), (n) })
#define field0_pair_prod_MDArr_nat(x) ((x).D)
#define field1_pair_prod_MDArr_nat(x) ((x).n)
".

CodeGen Inductive Type ((MDArr * MDArr) * nat)%type => "prod_prod_MDArr_MDArr_nat".
CodeGen Inductive Match ((MDArr * MDArr) * nat)%type => ""
| pair => "" "field0_pair_prod_prod_MDArr_MDArr_nat" "field1_pair_prod_prod_MDArr_MDArr_nat".
CodeGen Primitive pair (MDArr * MDArr)%type nat => "pair_prod_MDArr_MDArr_nat".
CodeGen Snippet "
typedef struct {
  prod_MDArr_MDArr D12;
  nat n;
} prod_prod_MDArr_MDArr_nat;
#define pair_prod_MDArr_MDArr_nat(D12, n) \
  ((prod_prod_MDArr_MDArr_nat){ (D12), (n) })
#define field0_pair_prod_prod_MDArr_MDArr_nat(x) ((x).D12)
#define field1_pair_prod_prod_MDArr_MDArr_nat(x) ((x).n)
".

CodeGen Inductive Type Aux => "Aux".
CodeGen Inductive Match Aux => ""
| mkAux => "" "get_query_bit" "get_input_bits" "get_blksz2" "get_ratio" "get_dir1" "get_dir2".
CodeGen Primitive mkAux => "mkAux".
CodeGen Primitive query_bit => "get_query_bit".
CodeGen Primitive input_bits => "get_input_bits".
CodeGen Primitive blksz2 => "get_blksz2".
CodeGen Primitive ratio => "get_ratio".
CodeGen Primitive dir1 => "get_dir1".
CodeGen Primitive dir2 => "get_dir2".
CodeGen Snippet "
typedef struct {
  bool query_bit;
  bits input_bits;
  nat ratio;
  nat blksz2;
  DArr dir1;
  DArr dir2;
} Aux;
#define mkAux(b, s, k, sz2, D1, D2) ((Aux){ (b), (s), (k), (sz2), (D1), (D2) })
#define get_query_bit(aux) ((aux).query_bit)
#define get_input_bits(aux) ((aux).input_bits)
#define get_blksz2(aux) ((aux).blksz2)
#define get_ratio(aux) ((aux).ratio)
#define get_dir1(aux) ((aux).dir1)
#define get_dir2(aux) ((aux).dir2)
".

CodeGen Function Nat.pred.
CodeGen Function neq0.
CodeGen Function buildDir2.
CodeGen Function buildDir1.
CodeGen Function buildDir.
CodeGen Function rank_init.
CodeGen Function rank_lookup.

CodeGen GenerateFile "sample/rank_proved.c".

(*
CodeGen Terminate Monomorphization addn.
CodeGen Terminate Monomorphization subn.
CodeGen Terminate Monomorphization muln.
CodeGen Terminate Monomorphization divn.
CodeGen Terminate Monomorphization modn.
CodeGen Terminate Monomorphization bitlen.
CodeGen Terminate Monomorphization bcount.
CodeGen Terminate Monomorphization eqb.
CodeGen Terminate Monomorphization negb.
CodeGen Terminate Monomorphization eqn.
CodeGen Monomorphization rank_init.
CodeGen Monomorphization rank_lookup.

Print _buildDir2.
Print _buildDir1.
Print _buildDir.
Print _rank_init.
Print _rank_lookup.
*)


(* GenCFile checks them internaly
CodeGen LinearCheck _pred _neq0.
CodeGen LinearCheck _buildDir2.
CodeGen LinearCheck _buildDir1.
CodeGen LinearCheck _buildDir.
CodeGen LinearCheck _rank_init.
CodeGen LinearCheck _rank_lookup.
*)

(*
CodeGen GenCFile "sample/rank_proved.c"
  _pred
  _neq0
  _buildDir2
  _buildDir1
  _buildDir
  _rank_init
  _rank_lookup.

*)
