
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

static nat
fastpow_iter(nat v1_a, nat v2_k, nat v3_x)
{
  nat v4_k_;
  bool v5_b;
  nat v6_n;
  nat v7_n;
  nat v8_n;
  entry_fixfunc1_fastpow_iter:
  switch (v2_k)
  {
    case 0:
      return v3_x;
    default:
      v4_k_ = nat_pred(v2_k);
      v5_b = odd(v2_k);
      switch (v5_b)
      {
        default:
          v6_n = muln(v1_a, v3_x);
          v2_k = v4_k_;
          v3_x = v6_n;
          goto entry_fixfunc1_fastpow_iter;
        case 0:
          v7_n = muln(v1_a, v1_a);
          v8_n = uphalf(v4_k_);
          v1_a = v7_n;
          v2_k = v8_n;
          goto entry_fixfunc1_fastpow_iter;
      }
  }
}
static nat
fastpow(nat v1_a, nat v2_k)
{
  nat v3_n;
  nat v4_n;
  v3_n = 0; v4_n = nat_succ(v3_n); return fastpow_iter(v1_a, v2_k, v4_n);
}
