Require Import codegen.codegen.

Require Import nat.
Require Import ascii.
Require Import str.

Require Import String.

CodeGen IndType string => "str_t" swfunc "str_sw" with
| EmptyString => case "0"
| String => case "" accessor "str_head" "str_tail".

CodeGen Primitive EmptyString => "str_empty".
CodeGen NoFunc String.

CodeGen Primitive eqstr => "eqstr".
CodeGen Primitive nthstr => "nthstr".
CodeGen Primitive takestr => "takestr".
CodeGen Primitive dropstr => "dropstr".
CodeGen Primitive takestrr => "takestrr".
CodeGen Primitive dropstrr => "dropstrr".
