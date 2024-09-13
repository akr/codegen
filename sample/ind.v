From codegen Require Import codegen.

CodeGen IndType bool => "bool" swfunc "" with
| true => constant "true" case ""
| false => constant "false" case "0".
Print CodeGen Inductive bool.

CodeGen IndType nat => "nat" swfunc "" with
| O => constant "0" case "0"
| S => primitive "succn" case "" accessor "predn".
Print CodeGen Inductive nat.

CodeGen IndType (option bool) => "int" swfunc "" with
| None => constant "(-1)" case "-1"
| Some => primitive "(int)" case "" accessor "".
Print CodeGen Inductive (option bool).

Definition opt_bool := option bool.
Print CodeGen Inductive (option bool).

Print CodeGen Inductive.

CodeGen Func Nat.add.
CodeGen Gen "add".
