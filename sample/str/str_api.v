Require Import codegen.codegen.

Require Import nat.
Require Import ascii.
Require Import str.

Require Import String.

CodeGen InductiveType string => "str_t".
CodeGen InductiveMatch string => "str_sw" with
| EmptyString => "0"
| String => "" "str_head" "str_tail".

CodeGen Primitive EmptyString => "str_empty".
CodeGen NoFunc String.

CodeGen Primitive eqstr => "eqstr".
