From codegen Require Import codegen.

CodeGen InductiveType bool => "bool".
CodeGen InductiveMatch bool => "" with
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".
Print CodeGen Inductive bool.

CodeGen InductiveType nat => "nat".
CodeGen InductiveMatch nat => "" with
| O => "case 0"
| S => "default" "predn".
CodeGen Constant O => "0".
CodeGen Primitive S => "succn".
Print CodeGen Inductive nat.

CodeGen InductiveType (option bool) => "int".
CodeGen InductiveMatch (option bool) => "" with
| None => "case -1"
| Some => "default" "".
CodeGen Constant None bool => "(-1)".
CodeGen Primitive Some bool => "(int)".
Print CodeGen Inductive (option bool).

Definition opt_bool := option bool.
Print CodeGen Inductive (option bool).

Print CodeGen Inductive.

CodeGen Func Nat.add.
CodeGen Gen "add".
