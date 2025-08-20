Require Import codegen.codegen.

(* C-level API configurations *)

CodeGen IndType nat => "uint64_t" swfunc "" with
| O => constant "0" case "0"
| S => primitive "nat_succ" case "" accessor "nat_pred".

CodeGen Primitive Nat.add => "nat_add".
CodeGen Primitive Nat.sub => "nat_sub".
CodeGen Primitive Nat.mul => "nat_mul".
CodeGen Primitive Nat.div => "nat_div".
CodeGen Primitive Nat.modulo => "nat_mod".
CodeGen Primitive Nat.double => "nat_double".
CodeGen Primitive Nat.div2 => "nat_div2".
CodeGen Primitive Nat.testbit => "nat_testbit".
CodeGen Primitive Nat.shiftl => "nat_shiftl".
CodeGen Primitive Nat.shiftr => "nat_shiftr".
CodeGen Primitive Nat.land => "nat_land".
CodeGen Primitive Nat.lor => "nat_lor".
CodeGen Primitive Nat.ldiff => "nat_ldiff".
CodeGen Primitive Nat.lxor => "nat_lxor".
CodeGen Primitive Nat.eqb => "nat_eqb".
CodeGen Primitive Nat.leb => "nat_leb".
CodeGen Primitive Nat.ltb => "nat_ltb".

(* C code generation part *)

CodeGen HeaderFile "nat.h".
CodeGen SourceFile "nat.c".

CodeGen HeaderSnippet "prologue" "
#ifndef NAT_H
#define NAT_H
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
