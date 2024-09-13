Require Import String.
Require Import Ascii.
Require Import Arith.
Require Import List.

Open Scope string_scope. (* enable "string-literal" and str ++ str *)

Definition string_of_bool (b : bool) : string :=
  match b with
  | true => "true"
  | false => "false"
  end.

Fixpoint digits_of_nat_rec (r : nat) (n : nat) (fuel : nat) : list nat :=
  match fuel with
  | O => nil (* should not happen *)
  | S fuel =>
      match n with
      | O => nil
      | S _ => (n mod r) :: (digits_of_nat_rec r (n / 10) fuel)
      end
  end.

(*
  digits_of_nat 10 0 = nil
  digits_of_nat 10 42 = 2 :: 4 :: nil
*)
Definition digits_of_nat (r : nat) (n : nat) : list nat :=
  digits_of_nat_rec r n n.

Definition digits10 : list ascii :=
 "0"%char :: "1"%char :: "2"%char :: "3"%char :: "4"%char ::
 "5"%char :: "6"%char :: "7"%char :: "8"%char :: "9"%char :: nil.

(*
  string_of_nat 0 = "0"
  string_of_nat 42 = "42"
*)
Definition string_of_nat (n : nat) : string :=
  match n with
  | O => "0"
  | S _ => fold_left (fun s i => String (nth i digits10 "0"%char) s) (digits_of_nat 10 n) EmptyString
  end.

Inductive buffer : Set := Buf : string -> buffer.
Definition bufcontent buf := match buf with Buf s => s end.
Definition mkbuf (initial_size : nat) := Buf "".
Definition buf_addch buf c := Buf (bufcontent buf ++ String c EmptyString).
Definition buf_addstr buf s := Buf (bufcontent buf ++ s).
Definition buf_addnat buf n := Buf (bufcontent buf ++ string_of_nat n).
Definition buf_addbool buf b := Buf (bufcontent buf ++ string_of_bool b).

Fixpoint sprintf_type (fmt : string) : Type :=
  match fmt with
  | EmptyString => buffer
  | String "%"%char (String "d"%char rest) => nat -> sprintf_type rest
  | String "%"%char (String "b"%char rest) => bool -> sprintf_type rest
  | String "%"%char (String "s"%char rest) => string -> sprintf_type rest
  | String "%"%char (String _ rest) => sprintf_type rest
  | String "%"%char EmptyString => buffer
  | String _ rest => sprintf_type rest
  end.

Fixpoint sprintf (buf : buffer) (fmt : string) {struct fmt} : sprintf_type fmt :=
  match fmt return sprintf_type fmt with
  | EmptyString => buf
  | String "%"%char (String "d"%char rest) => fun (n : nat) => sprintf (buf_addnat buf n) rest
  | String "%"%char (String "b"%char rest) => fun (b : bool) => sprintf (buf_addbool buf b) rest
  | String "%"%char (String "s"%char rest) => fun (s : string) => sprintf (buf_addstr buf s) rest
  | String "%"%char (String ch rest) => sprintf (buf_addch (buf_addch buf "%") ch) rest
  | String "%"%char EmptyString => buf_addch buf "%"%char
  | String ch rest => sprintf (buf_addch buf ch) rest
  end.

Compute sprintf (mkbuf 0) "foo" : buffer.
Compute sprintf (mkbuf 0) "bool:%b" true : buffer.
Compute sprintf (mkbuf 0) "bool:%b nat:%d" true 42 : buffer.

Require Import codegen.codegen.

CodeGen SourceFile "sample/sprintf_generated.c".

CodeGen IndType bool => "bool" swfunc "" with
| true => constant "true" case ""
| false => constant "false" case "0".

CodeGen IndType nat => "nat" swfunc "" with
| O => constant "0" case "0"
| S => primitive "nat_succ" case "" accessor "nat_pred".

CodeGen Primitive Nat.add => "nat_add".
CodeGen Primitive Nat.sub => "nat_sub".
CodeGen Primitive Nat.mul => "nat_mul".
CodeGen Primitive Nat.div => "nat_div".
CodeGen Primitive Nat.modulo => "nat_mod".

CodeGen IndType ascii => "unsigned char" with Ascii => primitive "make_char".
CodeGen IndType buffer => "buffer".

CodeGen Primitive mkbuf => "make_buffer".
CodeGen Primitive buf_addch => "buf_addch".
CodeGen Primitive buf_addnat => "buf_addnat".
CodeGen Primitive buf_addbool => "buf_addbool".

Definition add_mesg a b := sprintf (mkbuf 0) "%d + %d is %d" a b (a + b).
Check add_mesg.

CodeGen Linear buffer.
CodeGen Func sprintf _ "%d + %d is %d".
CodeGen Func add_mesg.

(*Set Debug CodeGen Simplification.
Set Debug CodeGen Reduction.*)
CodeGen GenerateFile.
