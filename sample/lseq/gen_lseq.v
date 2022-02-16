Require Import lseq.

Require Import codegen.codegen.

CodeGen BorrowFunction borrow_lseq_bool.

CodeGen Source File "lseq.c".
CodeGen Header File "lseq.h".

CodeGen Header Snippet "#ifndef LSEQ_H".
CodeGen Header Snippet "#define LSEQ_H".

CodeGen Snippet "#include ""lseq.h""".

CodeGen Inductive Type unit => "void".
CodeGen Inductive Match unit => ""
| tt => "0".
CodeGen Constant tt => "0".

CodeGen Inductive Type bool => "bool".
CodeGen Inductive Match bool => ""
| true => "default"
| false => "case 0".
CodeGen Constant true => "true".
CodeGen Constant false => "false".

CodeGen Header Snippet "
#include <stdbool.h> /* for bool, true and false */
".

CodeGen Inductive Type nat => "nat".
CodeGen Inductive Match nat => ""
| O => "case 0"
| S => "default" "nat_pred".
CodeGen Constant O => "0".
CodeGen Primitive S => "nat_succ".

CodeGen Header Snippet "
#include <stdint.h>
typedef uint64_t nat;
".

CodeGen Snippet "
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

CodeGen Snippet "
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

CodeGen Inductive Type lseq bool => "lseq_bool".
CodeGen Inductive Match lseq bool => "lseq_bool_is_nil"
| lnil => "default"
| lcons => "case 0" "lseq_bool_head" "lseq_bool_tail".
CodeGen Constant lnil bool => "((lseq_bool)NULL)".
CodeGen Primitive lcons bool => "lseq_bool_cons".
CodeGen Deallocator lcons bool => "free".

CodeGen Header Snippet "
#include <stdlib.h> /* for NULL, malloc(), abort() */

struct lseq_bool_struct;
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

CodeGen Function lseq_consume bool => "lseq_consume_bool".

CodeGen Inductive Type bseq bool => "lseq_bool".
CodeGen Inductive Match bseq bool => "lseq_bool_is_nil"
| bnil => "default"
| bcons => "case 0" "lseq_bool_head" "lseq_bool_tail".


CodeGen Function lncons bool => "lncons_bool".
CodeGen Function lnseq bool => "lnseq_bool".

CodeGen Function bhead bool => "bhead_bool".
CodeGen Function lbehead bool => "lbehead_bool".
CodeGen Function blast bool => "blast_bool".
CodeGen Function lbelast bool => "lbelast_bool".

CodeGen Function bsize bool => "bsize_bool".

CodeGen Function bnth bool => "bnth_bool".
CodeGen Function lset_nth bool => "lset_nth_bool".

CodeGen Function bnilp bool => "bnilp_bool".

CodeGen Function lmask bool => "lmask_bool".
CodeGen Function lcat bool => "lcat_bool".
CodeGen Function blcat bool => "blcat_bool".

CodeGen Function ltake bool => "ltake_bool".
CodeGen Function ldrop bool => "ldrop_bool".
CodeGen Function bdrop bool => "bdrop_bool".
CodeGen Function lrot bool => "lrot_bool".
CodeGen Function lrotr bool => "lrotr_bool".

CodeGen Function lcatrev bool => "lcatrev_bool".
CodeGen Function lrev bool => "lrev_bool".
CodeGen Function bcatrev bool => "bcatrev_bool".
CodeGen Function brev bool => "brev_bool".

CodeGen Header Snippet "#endif /* LSEQ_H */".

CodeGen GenerateFile.
