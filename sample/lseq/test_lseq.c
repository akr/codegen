#include <stdio.h>
#include <assert.h>
#include "lseq.h"

void print_lseq_bool(lseq_bool s)
{
  if (s == NULL)
    printf("[]\n");
  else {
    char sep = '[';
    while (s != NULL) {
      printf("%c%s", sep, s->head ? "true" : "false");
      sep = ',';
      s = s->tail;
    }
    printf("]\n");
  }
}

int main(int argc, char *argv[])
{
  lseq_bool a0 = NULL;
  lseq_bool a1 = lseq_bool_cons(true, a0);
  lseq_bool a2 = lseq_bool_cons(false, a1);
  lseq_bool a3 = lseq_bool_cons(true, a2);
  lseq_bool a4 = lseq_bool_cons(true, a3);

  lseq_bool b0 = NULL;
  lseq_bool b1 = lseq_bool_cons(false, b0);
  lseq_bool b2 = lseq_bool_cons(true, b1);

  lseq_bool c0 = NULL;
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
