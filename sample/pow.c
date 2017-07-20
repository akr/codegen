#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

#include <stdbool.h> /* defines bool type */
#define n0_true() true
#define n0_false() false
#define sw_bool(b) (b)
#define case_true_bool default
#define case_false_bool case false

#define nat uint64_t
#define n0_O() ((nat)0)
#define n1_S(n) ((n)+1)
#define sw_nat(n) (n)
#define case_O_nat case 0
#define case_S_nat default
#define field0_S_nat(n) ((n)-1)

#define n2_addn(a,b) ((a)+(b))
#define n2_subn(a,b) ((a)-(b))
#define n2_muln(a,b) ((a)*(b))
#define n2_divn(a,b) ((a)/(b))
#define n2_modn(a,b) ((a)%(b))

#define n1_odd(n) ((n)&1)

/* (n)+1 in n1_uphalf_(n) doesn't cause integer overflow
 * because uphalf' is applied to k' which is k-1.  */
#define n1_uphalf_(n) (((n)+1)>>1)

#include "pow_proved.c"

uint64_t ipow(uint64_t a, uint64_t k)
{
  uint64_t res = 1;
  uint64_t i;
  for (i = 0; i < k; i++)
    res *= a;
  return res;
}

int main(int argc, char *argv[])
{
  int i, j;
  for (i = 0; i < 7; i++) {
    for (j = 0; j < 7; j++) {
      int result = (int)n2_fastpow(i, j);
      int expected = (int)ipow(i, j);
      if (result != expected) abort();
      printf("%d^%d=%-6d", i, j, result);
    }
    putchar('\n');
  }
  return 0;
}
