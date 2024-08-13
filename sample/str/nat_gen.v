Require Import codegen.codegen.

Load "nat_api.v".

CodeGen HeaderFile "nat.h".
CodeGen SourceFile "nat.c".

CodeGen HeaderSnippet "prologue" "
#ifdef NAT_H
#include <stdint.h> /* uint64_t */
".

CodeGen HeaderSnippet "type_decls" "
typedef uint64_t nat;
".

CodeGen HeaderSnippet "func_impls" "
#define nat_succ(n) ((n)+1)
#define nat_pred(n) ((n)-1)
#define nat_add(x,y) ((x) + (y))
#define nat_sub(x,y) ((x) - (y))
#define nat_mul(x,y) ((x) * (y))
static inline nat nat_div(nat x, nat y) { return y == 0 ? 0 : x / y; }
static inline nat nat_mod(nat x, nat y) { return y == 0 ? x : x % y; }
#define nat_double(x) ((x) << 1)
#define nat_div2(x) ((x) >> 1)
#define nat_testbit(x,y) (((x) >> (y)) & 1)
static inline nat nat_shiftl(nat x, nat y) { return 63 < y ? 0 : x << y; }
static inline nat nat_shiftr(nat x, nat y) { return 63 < y ? 0 : x >> y; }
#define nat_land(x,y) ((x) & (y))
#define nat_lor(x,y) ((x) | (y))
#define nat_ldiff(x,y) ((x) & ~(y))
#define nat_lxor(x,y) ((x) ^ (y))
#define nat_eqb(x,y) ((x) == (y))
#define nat_leb(x,y) ((x) <= (y))
#define nat_ltb(x,y) ((x) < (y))
".

CodeGen Snippet "prologue" "#include ""nat.h""".

CodeGen HeaderSnippet "epilogue" "#endif /* NAT_H */".
CodeGen GenerateFile.
