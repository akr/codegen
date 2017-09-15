Require Import codegen.codegen.

Definition plus_1_2 := 1 + 2.
Monomorphization plus_1_2.
Print _plus_1_2.

Definition foo :=
  let id := (fun (T : Type) (x : T) => x) in
  (id bool true, id nat 0).
Monomorphization foo.

Print _foo.
(*
_foo = 
let id := fun x : bool => x in
let id0 := fun x : nat => x in
let b := _true in
let b0 := id b in let n := _O in let n0 := id0 n in _pair_bool_nat b0 n0
     : bool * nat
*)

Module M.
Definition id (T : Type) (x : T) := x.

Definition bar :=
  (id bool true, id nat 0, id bool true).
Monomorphization bar.

Print _bar.
Print _id_bool.
Print _id_nat.

Definition baz := (id bool true, id nat 0).
Monomorphization baz.
Print _baz.

Goal _bar = (id bool true, id nat 0, id bool true).
reflexivity.
Qed.

Terminate Monomorphization id unit.
Print _id_unit.

Definition qux := id unit tt.
Monomorphization qux.
Print _qux.
Print _id_unit.

Definition zero := 0.
Monomorphization zero.
Print _zero.

Definition one := 1.
Monomorphization one.
Print _one.

Definition list1 := cons 1 nil.
Monomorphization list1.
Print _list1.

Goal _list1 = cons 1 nil.
reflexivity.
Qed.

Definition pair00 := (0, 0).
Monomorphization pair00.
Print _pair00.
