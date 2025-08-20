Require Import codegen.codegen.

(* C-level API configurations *)

CodeGen IndType bool => "bool" swfunc "" with
| true => constant "true" case "true"
| false => constant "false" case "false".

CodeGen Primitive andb => "bool_and".
CodeGen Primitive orb => "bool_or".
CodeGen Primitive implb => "bool_impl".
CodeGen Primitive xorb => "bool_xor".
CodeGen Primitive negb => "bool_neg".

(* C code generation part *)

CodeGen HeaderFile "bool.h".
CodeGen SourceFile "bool.c".

CodeGen HeaderSnippet "prologue" "
#ifndef BOOL_H
#define BOOL_H
#include <stdbool.h> /* bool, true, false */
".

CodeGen HeaderSnippet "func_impls" "
#define bool_and(x,y) ((x) && (y))
#define bool_or(x,y) ((x) || (y))
#define bool_impl(x,y) (!(x) || (y))
#define bool_xor(x,y) ((x) != (y))
#define bool_neg(x) (!(x))
".

CodeGen Snippet "prologue" "#include ""bool.h""".

CodeGen HeaderSnippet "epilogue" "#endif /* BOOL_H */".
CodeGen GenerateFile.
