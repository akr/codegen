#include <stdio.h>
#include <assert.h>
#include "lseq.h"

#define lseq_bool_is_nil(s) (lseq_bool_sw(s) == lseq_bool_nil_tag)
#define lseq_bool_is_cons(s) (lseq_bool_sw(s) == lseq_bool_cons_tag)

void print_lseq_bool(lseq_bool s)
{
  if (lseq_bool_is_nil(s))
    printf("[]\n");
  else {
    char sep = '[';
    while (lseq_bool_is_cons(s)) {
      printf("%c%s", sep, lseq_bool_head(s) ? "true" : "false");
      sep = ',';
      s = lseq_bool_tail(s);
    }
    printf("]\n");
  }
}

static inline bool lseq_bool_eq(lseq_bool s1, lseq_bool s2) {
  while (lseq_bool_is_cons(s1) && lseq_bool_is_cons(s2)) {
    if (lseq_bool_head(s1) != lseq_bool_head(s2)) return false;
    s1 = lseq_bool_tail(s1);
    s2 = lseq_bool_tail(s2);
  }
  return !(lseq_bool_is_cons(s1) || lseq_bool_is_cons(s2));
}

int main(int argc, char *argv[])
{
  lseq_bool a0 = lseq_bool_nil();
  lseq_bool a1 = lseq_bool_cons(true, a0);
  lseq_bool a2 = lseq_bool_cons(false, a1);
  lseq_bool a3 = lseq_bool_cons(true, a2);
  lseq_bool a4 = lseq_bool_cons(true, a3);

  lseq_bool b0 = lseq_bool_nil();
  lseq_bool b1 = lseq_bool_cons(false, b0);
  lseq_bool b2 = lseq_bool_cons(true, b1);

  lseq_bool c0 = lseq_bool_nil();
  lseq_bool c1 = lseq_bool_cons(false, c0);
  lseq_bool c2 = lseq_bool_cons(true, c1);
  lseq_bool c3 = lseq_bool_cons(true, c2);
  lseq_bool c4 = lseq_bool_cons(false, c3);
  lseq_bool c5 = lseq_bool_cons(true, c4);
  lseq_bool c6 = lseq_bool_cons(true, c5);

  lseq_bool d = lcat_bool(a4, b2);

  assert(lseq_bool_eq(c6, d));

  print_lseq_bool(d);

  lseq_consume_bool(c6);
  lseq_consume_bool(d);
}
