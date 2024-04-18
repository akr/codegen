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

Note that buildDir, rank_init and rank_lookup is generated
using Coq and monomorphization plugin.
*/

/* hand written preamble */
/* not efficient */

#include <stdlib.h>
#include <stdbool.h> /* bool, true, false */
#include <stdint.h> /* uint64_t */
#include <stdio.h>
#include <string.h>
#include <limits.h>
#include <time.h>
#include <assert.h>
#include <unistd.h>
#include <inttypes.h>

typedef uint64_t nat;
#define succn(n) ((n)+1)
#define predn(n) ((n)-1)
#define addn(x,y) ((x) + (y))
#define subn(x,y) ((x) - (y))
#define muln(x,y) ((x) * (y))
#define divn(x,y) ((x) / (y))
#define modn(x,y) ((x) % (y))

typedef struct {
  uint64_t *buf;
  nat len; /* current length [bit] */
  nat max; /* maximum length [bit] */
} *bits;

#define bsize(s) ((s)->len)

bits alloc_bits(nat max)
{
  bits s;
  s = malloc(sizeof(*s));
  if (s == NULL) { perror("malloc"); exit(EXIT_FAILURE); }
  max = ((max + 63) / 64 * 64); /* aligned up to 64bit */
  if (max == 0) max = 64; /* avoid malloc(0) which is implementation-defined */
  s->buf = malloc(max / CHAR_BIT);
  if (s->buf == NULL) { perror("malloc"); exit(EXIT_FAILURE); }
  s->len = 0;
  s->max = max;
  return s;
}

bool get_bit(bits s, nat i)
{
  assert(i < s->len);
  return (s->buf[i / 64] >> (i % 64)) & 1;
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
  if (s->max <= s->len) {
    uint64_t *buf;
    nat max;
    max = s->max * 2;
    assert(s->max < max);
    buf = realloc(s->buf, max / CHAR_BIT);
    if (buf == NULL) { perror("realloc"); exit(EXIT_FAILURE); }
    s->buf = buf;
    s->max = max;
  }

  if (b)
    s->buf[s->len / 64] |= (uint64_t)1 << (s->len % 64);
  else
    s->buf[s->len / 64] &= ~((uint64_t)1 << (s->len % 64));
  s->len++;
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

nat bcount(bool b, nat n, nat m, bits bs)
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
#define MDArr DArr
#define dealloc_MDArr(x)

DArr emptyD(nat w)
{
  DArr d;
  assert(0 < w);
  d.w = w;
  d.s = alloc_bits(0);
  return d;
}

#define bwidth(d) ((d).w)

DArr pushD(DArr d, nat n)
{
  d.s = add_bits(d.s, d.w, n);
  return d;
}

#define freezeD(D) (D)

#define lookupD(d, i) get_bits((d).s, (d).w, (i) * (d).w)
#define sizeD(d) (bsize(d) / (d).w)

static inline nat
bitlen(nat n)
{
  if (n == 0) return 0;
  assert(64 <= sizeof(long) * CHAR_BIT);
  return 64 - __builtin_clzl(n);
}

#include "rank_generated.c"

/* main routine */

void print_bits(bits s)
{
  nat n = bsize(s);
  nat i;
  for (i = 0; i < n; i++)
    putchar(get_bit(s, i) ? '1' : '0');
}

int64_t difftimespec(struct timespec t1, struct timespec t2)
{
  return ((int64_t)t2.tv_sec - (int64_t)t1.tv_sec) * 1000000000 +
    (t2.tv_nsec - t1.tv_nsec);
}

void test_one(bits s, nat i)
{
  int res;
  nat m;
  struct timespec t1, t2;

  if (bsize(s) < i) {
    fprintf(stderr, "index too big\n");
    exit(EXIT_FAILURE);
  }

  Aux aux = rank_init(1, s);
  res = clock_gettime(CLOCK_THREAD_CPUTIME_ID, &t1);
  if (res == -1) { perror("clock_gettime"); exit(EXIT_FAILURE); }
  m = rank_lookup(aux, i);
  res = clock_gettime(CLOCK_THREAD_CPUTIME_ID, &t2);
  if (res == -1) { perror("clock_gettime"); exit(EXIT_FAILURE); }
  assert (m == bcount(1, 0, i, s));
  printf("rank(%lu) = %lu (%"PRId64"[ns])\n", i, m, difftimespec(t1, t2));
}

void test_all(bits s)
{
  Aux aux = rank_init(1, s);
  nat n = bsize(s);
  nat i;
  struct timespec t1, t2;
  for (i = 0; i <= n; i++) {
    int res;
    nat m;
    res = clock_gettime(CLOCK_THREAD_CPUTIME_ID, &t1);
    if (res == -1) { perror("clock_gettime"); exit(EXIT_FAILURE); }
    m = rank_lookup(aux, i);
    res = clock_gettime(CLOCK_THREAD_CPUTIME_ID, &t2);
    if (res == -1) { perror("clock_gettime"); exit(EXIT_FAILURE); }
    assert (m == bcount(1, 0, i, s));
    printf("rank(%lu) = %lu (%"PRId64"[ns])\n", i, m, difftimespec(t1, t2));
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
