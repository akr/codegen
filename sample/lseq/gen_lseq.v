Require Import lseq.

Require Import codegen.codegen.

CodeGen BorrowFunc borrow_lseq_bool.

CodeGen SourceFile "lseq.c".
CodeGen HeaderFile "lseq.h".

CodeGen HeaderSnippet "prologue" "#ifndef LSEQ_H".
CodeGen HeaderSnippet "prologue" "#define LSEQ_H".

CodeGen Snippet "prologue" "#include ""lseq.h""".

CodeGen InductiveType unit => "void".

CodeGen InductiveType bool => "bool".
CodeGen InductiveMatch bool => "" with
| true => ""
| false => "0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

CodeGen HeaderSnippet "prologue" "
#include <stdbool.h> /* for bool, true and false */
".

CodeGen InductiveType nat => "nat".
CodeGen InductiveMatch nat => "" with
| O => "0"
| S => "" "nat_pred".
CodeGen Constant O => "0".
CodeGen Primitive S => "nat_succ".

CodeGen HeaderSnippet "prologue" "
#include <stdint.h>
typedef uint64_t nat;
".

CodeGen Snippet "prologue" "
#define nat_succ(n) ((n)+1)
#define nat_pred(n) ((n)-1)
".

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

CodeGen Snippet "prologue" "
#define nat_add(x,y) ((x) + (y))
#define nat_sub(x,y) ((x) - (y))
#define nat_mul(x,y) ((x) * (y))
#define nat_div(x,y) ((x) / (y))
#define nat_mod(x,y) ((x) % (y))
#define nat_double(x) ((x) << 1)
#define nat_div2(x) ((x) >> 1)
#define nat_testbit(x,y) (((x) >> (y)) & 1)
#define nat_shiftl(x,y) ((x) << (y))
#define nat_shiftr(x,y) ((x) >> (y))
#define nat_land(x,y) ((x) & (y))
#define nat_lor(x,y) ((x) | (y))
#define nat_ldiff(x,y) ((x) & ~(y))
#define nat_lxor(x,y) ((x) ^ (y))
#define nat_eqb(x,y) ((x) == (y))
#define nat_leb(x,y) ((x) <= (y))
#define nat_ltb(x,y) ((x) < (y))
".

CodeGen InductiveType lseq bool => "lseq_bool".
CodeGen InductiveMatch lseq bool => "lseq_bool_is_nil" with
| lnil => ""
| lcons => "0" "lseq_bool_head" "lseq_bool_tail".
CodeGen Constant lnil bool => "((lseq_bool)NULL)".
CodeGen Primitive lcons bool => "lseq_bool_cons".
CodeGen InductiveDeallocator lseq bool with lnil => "" | lcons => "free".

CodeGen HeaderSnippet "prologue" "
#include <stdlib.h> /* for NULL, malloc(), abort() */

typedef struct lseq_bool_struct *lseq_bool;
struct lseq_bool_struct {
  bool head;
  lseq_bool tail;
};

static inline bool lseq_bool_is_nil(lseq_bool s) { return s == NULL; }
static inline bool lseq_bool_head(lseq_bool s) { return s->head; }
static inline lseq_bool lseq_bool_tail(lseq_bool s) { return s->tail; }
static inline lseq_bool lseq_bool_cons(bool v, lseq_bool s) {
  lseq_bool ret = malloc(sizeof(struct lseq_bool_struct));
  if (ret == NULL) abort();
  ret->head = v;
  ret->tail = s;
  return ret;
}
static inline bool lseq_bool_eq(lseq_bool s1, lseq_bool s2) {
  while (s1 && s2) {
    if (s1->head != s2->head) return false;
    s1 = s1->tail;
    s2 = s2->tail;
  }
  return !(s1 || s2);
}
".

CodeGen Func lseq_consume bool => "lseq_consume_bool".

CodeGen InductiveType bseq bool => "lseq_bool".
CodeGen InductiveMatch bseq bool => "lseq_bool_is_nil" with
| bnil => ""
| bcons => "0" "lseq_bool_head" "lseq_bool_tail".


CodeGen Func lncons bool => "lncons_bool".
CodeGen Func lnseq bool => "lnseq_bool".

CodeGen Func bhead bool => "bhead_bool".
CodeGen Func lbehead bool => "lbehead_bool".
CodeGen Func blast bool => "blast_bool".
CodeGen Func lbelast bool => "lbelast_bool".

CodeGen Func bsize bool => "bsize_bool".

CodeGen Func bnth bool => "bnth_bool".
CodeGen Func lset_nth bool => "lset_nth_bool".

CodeGen Func bnilp bool => "bnilp_bool".

CodeGen Func lmask bool => "lmask_bool".
CodeGen Func lcat bool => "lcat_bool".
CodeGen Func blcat bool => "blcat_bool".

CodeGen Func ltake bool => "ltake_bool".
CodeGen Func ldrop bool => "ldrop_bool".
CodeGen Func bdrop bool => "bdrop_bool".
CodeGen Func lrot bool => "lrot_bool".
CodeGen Func lrotr bool => "lrotr_bool".

CodeGen Func lcatrev bool => "lcatrev_bool".
CodeGen Func lrev bool => "lrev_bool".
CodeGen Func bcatrev bool => "bcatrev_bool".
CodeGen Func brev bool => "brev_bool".

CodeGen HeaderSnippet "epilogue" "#endif /* LSEQ_H */".

CodeGen GenerateFile.
