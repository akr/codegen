Require Import codegen.codegen.

Load "bool_api.v".
Load "nat_api.v".
Load "ascii_api.v".
Load "str_api.v".

CodeGen HeaderFile "str.h".
CodeGen SourceFile "str.c".

CodeGen HeaderSnippet "prologue" "
#ifdef STR_H
#include ""nat.h""
#include ""ascii.h""
".

CodeGen HeaderSnippet "type_impls" "
typedef struct {
  unsigned char *ptr;
  uint64_t size;
} str_t;
#define str_sw(x) ((x).size)
#define str_head(x) (*(x).ptr)
static inline str_t str_tail(str_t x) { return (str_t){ x.ptr+1, x.size-1 }; }
#define str_empty() ((str_t){ (unsigned char *)0, 0 })
".


Fixpoint mystrlen (x : string) : nat :=
  match x with
  | EmptyString => 0
  | String _ t => S (mystrlen t)
  end.

CodeGen Func mystrlen.


CodeGen HeaderSnippet "epilogue" "#endif /* STR_H */".


CodeGen GenerateFile.



