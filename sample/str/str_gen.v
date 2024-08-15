Require Import codegen.codegen.

Load "bool_api.v".
Load "nat_api.v".
Load "ascii_api.v".
Load "str_api.v".

CodeGen HeaderFile "str.h".
CodeGen SourceFile "str.c".

CodeGen HeaderSnippet "prologue" "
#ifndef STR_H
#define STR_H
#include <stdbool.h>
#include <string.h>
#include ""nat.h""
#include ""ascii.h""
".

CodeGen HeaderSnippet "type_impls" "
typedef struct {
  uint8_t *ptr;
  uint64_t size;
} str_t;
#define str_sw(x) ((x).size)
#define str_head(x) (*(x).ptr)
static inline str_t str_tail(str_t x) { return (str_t){ x.ptr+1, x.size-1 }; }
#define str_empty() ((str_t){ (uint8_t *)0, 0 })
static inline bool eqstr(str_t x, str_t y) { return x.size == y.size && memcmp(x.ptr, y.ptr, x.size) == 0; }
static inline uint8_t nthstr(str_t s, nat i) { return s.size <= i ? 0 : s.ptr[i]; }
static inline str_t takestr(nat n, str_t s) { if (s.size < n) n = s.size; return (str_t){ s.ptr, n }; }
static inline str_t dropstr(nat n, str_t s) { if (s.size < n) n = s.size; return (str_t){ s.ptr+n, s.size-n }; }
static inline str_t takestrr(nat n, str_t s) { if (s.size < n) n = s.size; return (str_t){ s.ptr+(s.size-n), n }; }
static inline str_t dropstrr(nat n, str_t s) { if (s.size < n) n = s.size; return (str_t){ s.ptr, s.size-n }; }
".

CodeGen Snippet "prologue" "#include ""str.h""".

Fixpoint mystrlen (x : string) : nat :=
  match x with
  | EmptyString => 0
  | String _ t => S (mystrlen t)
  end.

CodeGen Func mystrlen.


CodeGen HeaderSnippet "epilogue" "#endif /* STR_H */".

CodeGen GenerateFile.



