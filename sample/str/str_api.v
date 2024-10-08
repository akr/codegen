Require Import codegen.codegen.

Require Import nat.
Require Import ascii.
Require Import str.

Require Import String.

CodeGen IndType string => "str_t" swfunc "str_sw" with
| EmptyString => primitive "str_empty" case "0"
| String => nofunc case "" accessor "str_head" "str_tail".

CodeGen Primitive eqstr => "eqstr".
CodeGen Primitive nthstr => "nthstr".
CodeGen Primitive takestr => "takestr".
CodeGen Primitive dropstr => "dropstr".
CodeGen Primitive takestrr => "takestrr".
CodeGen Primitive dropstrr => "dropstrr".
