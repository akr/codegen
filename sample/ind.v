From codegen Require Import codegen.

CodeGen IndType bool => "bool" swfunc "" with
| true => case ""
| false => case "0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".
Print CodeGen Inductive bool.

CodeGen IndType nat => "nat" swfunc "" with
| O => case "0"
| S => case "" accessor "predn".
CodeGen Constant O => "0".
CodeGen Primitive S => "succn".
Print CodeGen Inductive nat.

CodeGen IndType (option bool) => "int" swfunc "" with
| None => case "-1"
| Some => case "" accessor "".
CodeGen Constant @None bool => "(-1)".
CodeGen Primitive @Some bool => "(int)".
Print CodeGen Inductive (option bool).

Definition opt_bool := option bool.
Print CodeGen Inductive (option bool).

Print CodeGen Inductive.

CodeGen Func Nat.add.
CodeGen Gen "add".
