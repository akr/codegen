#include <stdbool.h> /* for bool, true and false */
#include <stdint.h> /* uint64_t */
#include <stddef.h> /* size_t */
#include <stdlib.h> /* malloc */
#include <stdio.h> /* perror */
#include <assert.h> /* assert */
#include <inttypes.h> /* PRIu64 */

typedef uint64_t nat;
#define nat_succ(n) ((n)+1)
#define nat_pred(n) ((n)-1)

#define nat_add(x,y) ((x) + (y))
#define nat_sub(x,y) ((x) - (y))
#define nat_mul(x,y) ((x) * (y))
#define nat_div(x,y) ((x) / (y))
#define nat_mod(x,y) ((x) % (y))

#define make_char(b0,b1,b2,b3,b4,b5,b6,b7) \
  ((b0) | (b1) << 1 | (b2) << 2 | (b3) << 3 | \
   (b4) << 4 | (b5) << 5 | (b6) << 6 | (b7) << 7)

typedef struct {
  unsigned char *mem;
  size_t len; /* current length */
  size_t max; /* maximum length */
} *buffer;

buffer make_buffer(nat max0)
{
  buffer buf;
  size_t max;
  buf = malloc(sizeof(*buf));
  if (buf == NULL) { perror("malloc"); exit(EXIT_FAILURE); }
  max = max0;
  if (max == 0) max = 16; /* avoid malloc(0) which is implementation-defined */
  buf->mem = malloc(max);
  if (buf->mem == NULL) { perror("malloc"); exit(EXIT_FAILURE); }
  buf->len = 0;
  buf->max = max;
  return buf;
}

buffer buf_addch(buffer buf, unsigned char c)
{
  if (buf->max <= buf->len) {
    unsigned char *mem;
    size_t max;
    max = buf->max * 2;
    assert(buf->max < max);
    mem = realloc(buf->mem, max);
    if (mem == NULL) { perror("realloc"); exit(EXIT_FAILURE); }
    buf->mem = mem;
    buf->max = max;
  }

  buf->mem[buf->len++] = c;
  return buf;
}

buffer buf_addbool(buffer buf, bool b)
{
  if (b) {
    buf_addch(buf, 't');
    buf_addch(buf, 'r');
    buf_addch(buf, 'u');
    buf_addch(buf, 'e');
  }
  else {
    buf_addch(buf, 'f');
    buf_addch(buf, 'a');
    buf_addch(buf, 'l');
    buf_addch(buf, 's');
    buf_addch(buf, 'e');
  }
  return buf;
}

buffer buf_addnat(buffer buf, nat n)
{
  char tmp[sizeof(n)*3+1], *p;
  sprintf(tmp, "%"PRIu64, n);
  for (p = tmp; *p; p++)
    buf_addch(buf, *(unsigned char *)p);
  return buf;
}

#include "sprintf_proved.c"

int main(int argc, char *argv[])
{
  buffer buf = add_mesg(1, 2);
  fwrite(buf->mem, 1, buf->len, stdout);
  putchar('\n');
  return 0;
}
