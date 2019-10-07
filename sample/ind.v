From codegen Require Import codegen.

CodeGen Inductive Type bool "bool".
CodeGen Inductive Constructor bool true "true".
CodeGen Inductive Constructor bool false "false".
CodeGen Inductive Match bool "" true "default" false "case 0".
Print CodeGen Inductive bool.

CodeGen Inductive Type nat "uint64_t".
CodeGen Inductive Constructor nat O "0".
CodeGen Inductive Constructor nat S "succ".
CodeGen Inductive Match nat "" O "case 0" S "default" "pred".
Print CodeGen Inductive nat.

CodeGen Inductive Type (option bool) "int".
CodeGen Inductive Constructor (option bool) None "(-1)".
CodeGen Inductive Constructor (option bool) Some "(int)".
CodeGen Inductive Match (option bool) "" None "case -1" Some "default" "".
Print CodeGen Inductive (option bool).

Definition opt_bool := option bool.
Print CodeGen Inductive (option bool).

Print CodeGen Inductive.

CodeGen Monomorphization Nat.add.
CodeGen GenC _add.