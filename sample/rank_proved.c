
#include <stdbool.h> /* for bool, true and false */


#include <stdint.h>
typedef uint64_t nat;
#define nat_succ(n) ((n)+1)
#define nat_pred(n) ((n)-1)


#define addn(x,y) ((x) + (y))
#define subn(x,y) ((x) - (y))
#define muln(x,y) ((x) * (y))
#define divn(x,y) ((x) / (y))
#define modn(x,y) ((x) % (y))


typedef struct {
  MDArr D1;
  MDArr D2;
} prod_MDArr_MDArr;
#define pair_MDArr_MDArr(D1, D2) ((prod_MDArr_MDArr){ (D1), (D2) })
#define field0_pair_prod_MDArr_MDArr(x) ((x).D1)
#define field1_pair_prod_MDArr_MDArr(x) ((x).D2)


typedef struct {
  MDArr D;
  nat n;
} prod_MDArr_nat;
#define pair_MDArr_nat(D, n) ((prod_MDArr_nat){ (D), (n) })
#define field0_pair_prod_MDArr_nat(x) ((x).D)
#define field1_pair_prod_MDArr_nat(x) ((x).n)


typedef struct {
  prod_MDArr_MDArr D12;
  nat n;
} prod_prod_MDArr_MDArr_nat;
#define pair_prod_MDArr_MDArr_nat(D12, n) \
  ((prod_prod_MDArr_MDArr_nat){ (D12), (n) })
#define field0_pair_prod_prod_MDArr_MDArr_nat(x) ((x).D12)
#define field1_pair_prod_prod_MDArr_MDArr_nat(x) ((x).n)


typedef struct {
  bool query_bit;
  bits input_bits;
  nat ratio;
  nat blksz2;
  DArr dir1;
  DArr dir2;
} Aux;
#define mkAux(b, s, k, sz2, D1, D2) ((Aux){ (b), (s), (k), (sz2), (D1), (D2) })
#define get_query_bit(aux) ((aux).query_bit)
#define get_input_bits(aux) ((aux).input_bits)
#define get_blksz2(aux) ((aux).blksz2)
#define get_ratio(aux) ((aux).ratio)
#define get_dir1(aux) ((aux).dir1)
#define get_dir2(aux) ((aux).dir2)

static nat
pred(nat v0_n)
{
  switch (v0_n)
  {
    case 0: { return v0_n; }
    default: { nat v1_u = nat_pred(v0_n); return v1_u; }
  }
}
static nat neq0(nat v0_n) { nat v1_n = pred(v0_n); return nat_succ(v1_n); }
static
prod_MDArr_nat
buildDir2(bool v0_b,
          bits v1_s,
          nat v2_sz2,
          nat v3_c,
          nat v4_i,
          MDArr v5_D2,
          nat v6_m2)
{
  entry_buildDir2:;
  switch (v3_c)
  {
    case 0: { return pair_MDArr_nat(v5_D2, v6_m2); }
    default: {
      nat v7_cp = nat_pred(v3_c);
      nat v8_m = bcount(v0_b, v4_i, v2_sz2, v1_s);
      nat v9_n = addn(v4_i, v2_sz2);
      MDArr v10_m = pushD(v5_D2, v6_m2);
      nat v11_n = addn(v6_m2, v8_m);
      v3_c = v7_cp;
      v4_i = v9_n;
      v5_D2 = v10_m;
      v6_m2 = v11_n;
      goto entry_buildDir2;
    }
  }
}
static
prod_prod_MDArr_MDArr_nat
buildDir1(bool v0_b,
          bits v1_s,
          nat v2_k,
          nat v3_sz1,
          nat v4_sz2,
          nat v5_c,
          nat v6_i,
          MDArr v7_D1,
          MDArr v8_D2,
          nat v9_m1)
{
  entry_buildDir1:;
  switch (v5_c)
  {
    case 0: {
      prod_MDArr_MDArr v10_p = pair_MDArr_MDArr(v7_D1, v8_D2);
      return pair_prod_MDArr_MDArr_nat(v10_p, v9_m1);
    }
    default: {
      nat v11_cp = nat_pred(v5_c);
      MDArr v12_D1_ = pushD(v7_D1, v9_m1);
      nat v13_n = 0;
      prod_MDArr_nat
      v14_p
      =
      buildDir2(v0_b,
      v1_s,
      v4_sz2,
      v2_k,
      v6_i,
      v8_D2,
      v13_n);
      MDArr v15_D2_ = field0_pair_prod_MDArr_nat(v14_p);
      nat v16_m2 = field1_pair_prod_MDArr_nat(v14_p);
      nat v17_n = addn(v6_i, v3_sz1);
      nat v18_n = addn(v9_m1, v16_m2);
      v5_c = v11_cp;
      v6_i = v17_n;
      v7_D1 = v12_D1_;
      v8_D2 = v15_D2_;
      v9_m1 = v18_n;
      goto entry_buildDir1;
    }
  }
}
static prod_MDArr_MDArr
buildDir(bool v0_b, bits v1_s, nat v2_k, nat v3_sz2, nat v4_w1, nat v5_w2)
{
  nat v6_sz1 = muln(v2_k, v3_sz2);
  nat v7_n = bsize(v1_s);
  nat v8_n2 = divn(v7_n, v3_sz2);
  nat v9_n1 = divn(v8_n2, v2_k);
  nat v10_n = 0;
  MDArr v11_m = emptyD(v4_w1);
  MDArr v12_m = emptyD(v5_w2);
  nat v13_n = 0;
  prod_prod_MDArr_MDArr_nat
  v14_p
  =
  buildDir1(v0_b,
  v1_s,
  v2_k,
  v6_sz1,
  v3_sz2,
  v9_n1,
  v10_n,
  v11_m,
  v12_m,
  v13_n);
  prod_MDArr_MDArr v15_p = field0_pair_prod_prod_MDArr_MDArr_nat(v14_p);
  nat v16_m1 = field1_pair_prod_prod_MDArr_MDArr_nat(v14_p);
  MDArr v17_D1 = field0_pair_prod_MDArr_MDArr(v15_p);
  MDArr v18_D2 = field1_pair_prod_MDArr_MDArr(v15_p);
  nat v19_n = modn(v8_n2, v2_k);
  nat v20_n = muln(v9_n1, v6_sz1);
  nat v21_n = 0;
  prod_MDArr_nat
  v22_p
  =
  buildDir2(v0_b,
  v1_s,
  v3_sz2,
  v19_n,
  v20_n,
  v18_D2,
  v21_n);
  MDArr v23_D2 = field0_pair_prod_MDArr_nat(v22_p);
  nat v24_m2 = field1_pair_prod_MDArr_nat(v22_p);
  MDArr v25_m = pushD(v17_D1, v16_m1);
  MDArr v26_m = pushD(v23_D2, v24_m2);
  return pair_MDArr_MDArr(v25_m, v26_m);
}
static Aux
rank_init(bool v0_b, bits v1_s)
{
  nat v2_n = bsize(v1_s);
  nat v3_kp = bitlen(v2_n);
  nat v4_k = nat_succ(v3_kp);
  nat v5_sz2p = bitlen(v2_n);
  nat v6_sz2 = nat_succ(v5_sz2p);
  nat v7_sz1 = muln(v4_k, v6_sz2);
  nat v8_n = divn(v2_n, v7_sz1);
  nat v9_n = muln(v8_n, v7_sz1);
  nat v10_n = bitlen(v9_n);
  nat v11_w1 = neq0(v10_n);
  nat v12_n = muln(v3_kp, v6_sz2);
  nat v13_n = bitlen(v12_n);
  nat v14_w2 = neq0(v13_n);
  prod_MDArr_MDArr
  v15_p
  =
  buildDir(v0_b,
  v1_s,
  v4_k,
  v6_sz2,
  v11_w1,
  v14_w2);
  MDArr v16_D1 = field0_pair_prod_MDArr_MDArr(v15_p);
  MDArr v17_D2 = field1_pair_prod_MDArr_MDArr(v15_p);
  DArr v18_d = freezeD(v16_D1);
  DArr v19_d = freezeD(v17_D2);
  return mkAux(v0_b, v1_s, v4_k, v6_sz2, v18_d, v19_d);
}
static nat
rank_lookup(Aux v0_aux, nat v1_i)
{
  bool v2_b = get_query_bit(v0_aux);
  bits v3_s = get_input_bits(v0_aux);
  nat v4_k = get_ratio(v0_aux);
  nat v5_sz2 = get_blksz2(v0_aux);
  DArr v6_D1 = get_dir1(v0_aux);
  DArr v7_D2 = get_dir2(v0_aux);
  nat v8_j2 = divn(v1_i, v5_sz2);
  nat v9_j3 = modn(v1_i, v5_sz2);
  nat v10_j1 = divn(v8_j2, v4_k);
  nat v11_n = lookupD(v6_D1, v10_j1);
  nat v12_n = lookupD(v7_D2, v8_j2);
  nat v13_n = addn(v11_n, v12_n);
  nat v14_n = muln(v8_j2, v5_sz2);
  nat v15_n = bcount(v2_b, v14_n, v9_j3, v3_s);
  return addn(v13_n, v15_n);
}
