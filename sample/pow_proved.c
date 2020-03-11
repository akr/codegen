
#include <stdbool.h> /* for bool, true and false */


#include <stdint.h>
typedef uint64_t nat;
#define nat_succ(n) ((n)+1)
#define nat_pred(n) ((n)-1)


#define muln(x,y) ((x) * (y))
#define odd(n) ((n)&1)

/* (n)+1 in uphalf(n) doesn't cause integer overflow
 * because uphalf' is applied to k' which is k-1.  */
#define uphalf(n) (((n)+1)>>1)

static
nat
fastpow_iter(nat v0_a, nat v1_k, nat v2_x)
{
  entry_fastpow_iter:;
  switch (v1_k)
  {
    case 0: { return v2_x; }
    default: {
      nat v3_k_ = nat_pred(v1_k);
      bool v4_b = odd(v1_k);
      switch (v4_b)
      {
        default: {
          nat v5_n = muln(v0_a, v2_x);
          v1_k = v3_k_;
          v2_x = v5_n;
          goto entry_fastpow_iter;
        }
        case 0: {
          nat v6_n = muln(v0_a, v0_a);
          nat v7_n = uphalf(v3_k_);
          v0_a = v6_n;
          v1_k = v7_n;
          goto entry_fastpow_iter;
        }
      }
    }
  }
}
static nat
fastpow(nat v0_a, nat v1_k)
{
  nat v2_n = 0;
  nat v3_n = nat_succ(v2_n);
  return fastpow_iter(v0_a, v1_k, v3_n);
}
