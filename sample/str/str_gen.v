Require Import codegen.codegen.

Load "bool_api.v".
Load "nat_api.v".
Load "ascii_api.v".
Load "str_api.v".

CodeGen HeaderFile "str.h".
CodeGen SourceFile "str.c".

CodeGen HeaderSnippet "prologue" "
#ifdef STR_H
#include <stdbool.h>
#include <string.h>
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
static inline bool eqstr(str_t x, str_t y) { return x.size == y.size && memcmp(x.ptr, y.ptr, x.size) == 0; }
static inline str_t takestr(nat n, str_t s) { if (s.size < n) n = s.size; return (str_t){ s.ptr, s.size-n }; }
static inline str_t dropstr(nat n, str_t s) { if (s.size < n) n = s.size; return (str_t){ s.ptr+n, s.size-n }; }
".

Fixpoint mystrlen (x : string) : nat :=
  match x with
  | EmptyString => 0
  | String _ t => S (mystrlen t)
  end.

CodeGen Func mystrlen.


CodeGen HeaderSnippet "epilogue" "#endif /* STR_H */".


CodeGen GenerateFile.



