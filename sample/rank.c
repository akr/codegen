/*
How to compile:

  with GC:
    sudo aptitude install libgc-dev      # Boehm-Demers-Weiser's GC
    gcc -Wall -O3 rank.c -lgc -o rank

  without GC (with memory leak):
    gcc -g -Wall rank.c -o rank

Usage:

  ./rand BITS [prefixlen]
  ./rand rand [totallen [prefixlen]]

Example:

  ./rank 10010101 5
  ./rank rand 10

Note that n11_buildDir, n2_rank_init and n2_rank_lookup is generated
using Coq and monomorphization plugin.
*/

/* hand written preamble */
/* not efficient */

#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <limits.h>
#include <time.h>
#include <assert.h>
#include <unistd.h>

#include <stdbool.h>
#define n0_true() true
#define n0_false() false

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

typedef struct {
  uint64_t *buf;
  nat len; /* current length [bit] */
  nat max; /* maximum length [bit] */
} bits_heap;

typedef struct {
  bits_heap *heap;
  nat len; /* expected length [bit] */
} bits;

#define n1_bsize(s) ((s).len)

bits alloc_bits(nat max)
{
  bits_heap *bh;
  bh = malloc(sizeof(bits_heap));
  if (bh == NULL) { perror("malloc"); exit(EXIT_FAILURE); }
  max = ((max + 63) / 64 * 64); /* aligned up to 64bit */
  if (max == 0) max = 64; /* avoid malloc(0) which is implementation-defined */
  bh->buf = malloc(max / CHAR_BIT);
  if (bh->buf == NULL) { perror("malloc"); exit(EXIT_FAILURE); }
  bh->len = 0;
  bh->max = max;
  bits s;
  s.heap = bh;
  s.len = 0;
  return s;
}

bits copy_prefix(bits s, nat n)
{
  nat max = (n + 63) / 64 * 64;
  if (max == 0) max = 64;
  bits s2 = alloc_bits(max);
  memcpy(s2.heap->buf, s.heap->buf, max / CHAR_BIT);
  s2.len = s2.heap->len = n;
  return s2;
}

bool get_bit(bits s, nat i)
{
  assert(i < s.len);
  return (s.heap->buf[i / 64] >> (i % 64)) & 1;
}

nat get_bits(bits s, nat w, nat i)
{
  nat n = 0;
  for (; 0 < w; w--)
    n = (n << 1) | get_bit(s, i + w - 1);
  return n;
}

bits add_bit(bits s, bool b)
{
  if (s.len != s.heap->len)
    s = copy_prefix(s, s.len);

  if (s.heap->max <= s.len) {
    uint64_t *buf;
    nat max;
    max = s.heap->max * 2;
    assert(s.heap->max < max);
    buf = realloc(s.heap->buf, max / CHAR_BIT);
    if (buf == NULL) { perror("realloc"); exit(EXIT_FAILURE); }
    s.heap->buf = buf;
    s.heap->max = max;
  }

  if (b)
    s.heap->buf[s.len / 64] |= (uint64_t)1 << (s.len % 64);
  else
    s.heap->buf[s.len / 64] &= ~((uint64_t)1 << (s.len % 64));
  s.len++;
  s.heap->len++;
  return s;
}

bits add_bits(bits s, nat w, nat n)
{
  for (; 0 < w; w--) {
    s = add_bit(s, n & 1);
    n >>= 1;
  }
  return s;
}

nat n4_bcount(bool b, nat n, nat m, bits bs)
{
  nat ret = 0;
  nat i;
  for (i = n; i < n + m; i++)
    if (get_bit(bs, i) == b)
      ret++;
  return ret;
}

typedef struct {
  nat w;
  bits s;
} DArr;

DArr n1_emptyD(nat w)
{
  DArr d;
  assert(0 < w);
  d.w = w;
  d.s = alloc_bits(0);
  return d;
}

#define n1_bwidth(d) ((d).w)

DArr n2_pushD(DArr d, nat n)
{
  d.s = add_bits(d.s, d.w, n);
  return d;
}

#define n2_lookupD(d, i) get_bits((d).s, (d).w, (i) * (d).w)
#define n1_sizeD(d) (n1_bsize(d) / (d).w)

typedef struct {
  DArr D1;
  DArr D2;
} prod_DArr_DArr;
#define n2_pair_DArr_DArr(D1, D2) ((prod_DArr_DArr){ (D1), (D2) })
#define field0_pair_prod_DArr_DArr(x) ((x).D1)
#define field1_pair_prod_DArr_DArr(x) ((x).D2)

typedef struct {
  DArr D;
  nat n;
} prod_DArr_nat;
#define n2_pair_DArr_nat(D, n) ((prod_DArr_nat){ (D), (n) })
#define field0_pair_prod_DArr_nat(x) ((x).D)
#define field1_pair_prod_DArr_nat(x) ((x).n)

typedef struct {
  prod_DArr_DArr D12;
  nat n;
} prod_prod_DArr_DArr_nat;
#define n2_pair_prod_DArr_DArr_nat(D12, n) \
  ((prod_prod_DArr_DArr_nat){ (D12), (n) })
#define field0_pair_prod_prod_DArr_DArr_nat(x) ((x).D12)
#define field1_pair_prod_prod_DArr_DArr_nat(x) ((x).n)

static inline nat
n1_bitlen(nat n)
{
  if (n == 0) return 0;
  assert(64 <= sizeof(long) * CHAR_BIT);
  return 64 - __builtin_clzl(n);
}

typedef struct {
  bool query_bit;
  bits input_bits;
  nat ratio;
  nat blksz2;
  DArr dir1;
  DArr dir2;
} Aux;
#define n6_mkAux(b, s, k, sz2, D1, D2) ((Aux){ (b), (s), (k), (sz2), (D1), (D2) })
#define n1_query_bit(aux) ((aux).query_bit)
#define n1_input_bits(aux) ((aux).input_bits)
#define n1_blksz2(aux) ((aux).blksz2)
#define n1_ratio(aux) ((aux).ratio)
#define n1_dir1(aux) ((aux).dir1)
#define n1_dir2(aux) ((aux).dir2)

#include "rank_proved.c"

/* main routine */

void print_bits(bits s)
{
  nat n = n1_bsize(s);
  nat i;
  for (i = 0; i < n; i++)
    putchar(get_bit(s, i) ? '1' : '0');
}

void test_one(bits s, nat i)
{
  if (n1_bsize(s) < i) {
    fprintf(stderr, "index too big\n");
    exit(EXIT_FAILURE);
  }

  Aux aux = n2_rank_init(1, s);
  nat m = n2_rank_lookup(aux, i);
  assert (m == n4_bcount(1, 0, i, s));
  printf("rank(%lu) = %lu\n", i, m);
}

void test_all(bits s)
{
  Aux aux = n2_rank_init(1, s);
  nat n = n1_bsize(s);
  nat i;
  for (i = 0; i <= n; i++) {
    nat m = n2_rank_lookup(aux, i);
    assert (m == n4_bcount(1, 0, i, s));
    printf("rank(%lu) = %lu\n", i, m);
  }
}

int main(int argc, char *argv[])
{
  if (argc <= 1) {
    fprintf(stderr,
        "usage: %s BITS [prefixlen]\n"
        "       %s rand [totallen [prefixlen]]\n",
        argv[0], argv[0]);
    exit(EXIT_FAILURE);
  }

  if (strcmp(argv[1], "rand") == 0) {
    srand((unsigned int)(time(NULL) + getpid()));
    nat n;
    if (argc <= 2)
      n = rand() % 1000;
    else
      n = strtoul(argv[2], NULL, 0);
    bits s = alloc_bits(n);
    while (1) {
      int r = rand(); /* [0, RAND_MAX] where 32767 <= RAND_MAX */
      if (15 < n) { /* 2**15 = 32768 */
        s = add_bits(s, 15, r);
        n -= 15;
      }
      else {
        s = add_bits(s, n, r);
        break;
      }
    }
    printf("s = ");
    print_bits(s);
    putchar('\n');

    if (argc <= 3)
      test_all(s);
    else {
      nat i = strtoul(argv[2], NULL, 0);
      test_one(s, i);
    }
  }
  else {
    char *str = argv[1];
    nat size = strlen(str);
    bits s = alloc_bits(size);
    nat i;
    for (i = 0; i < size; i++)
      s = add_bit(s, str[i] == '1');
    printf("s = ");
    print_bits(s);
    putchar('\n');

    if (argc <= 2)
      test_all(s);
    else {
      nat i = strtoul(argv[2], NULL, 0);
      test_one(s, i);
    }
  }

  return EXIT_SUCCESS;
}
