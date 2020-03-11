#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

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
      int result = (int)fastpow(i, j);
      int expected = (int)ipow(i, j);
      if (result != expected) abort();
      printf("%d^%d=%-6d", i, j, result);
    }
    putchar('\n');
  }
  return 0;
}
