Require Import codegen.codegen.

Load "bool_api.v".

CodeGen HeaderFile "bool.h".
CodeGen SourceFile "bool.c".

CodeGen HeaderSnippet "prologue" "
#ifdef BOOL_H
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
