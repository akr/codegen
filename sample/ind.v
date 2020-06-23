From codegen Require Import codegen.

CodeGen Inductive Type bool => "bool".
CodeGen Inductive Match bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".
Print CodeGen Inductive bool.

CodeGen Inductive Type nat => "nat".
CodeGen Inductive Match nat => ""
| O => "case 0"
| S => "default" "predn".
CodeGen Constant O => "0".
CodeGen Primitive S => "succn".
Print CodeGen Inductive nat.

CodeGen Inductive Type (option bool) => "int".
CodeGen Inductive Match (option bool) => ""
| None => "case -1"
| Some => "default" "".
CodeGen Constant None bool => "(-1)".
CodeGen Primitive Some bool => "(int)".
Print CodeGen Inductive (option bool).

Definition opt_bool := option bool.
Print CodeGen Inductive (option bool).

Print CodeGen Inductive.

CodeGen Function Nat.add.
CodeGen Gen "add".