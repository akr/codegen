Require Import codegen.codegen.

Require Import bool.

CodeGen IndType bool => "bool" swfunc "" with
| true => case "true"
| false => case "false".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

CodeGen Primitive andb => "bool_and".
CodeGen Primitive orb => "bool_or".
CodeGen Primitive implb => "bool_impl".
CodeGen Primitive xorb => "bool_xor".
CodeGen Primitive negb => "bool_neg".
