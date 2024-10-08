/* section-start: prologue */
/* section-end: prologue */
/* section-start: type_decls */
typedef struct g3_istruct_Aux *Aux;

/* section-end: type_decls */
/* section-start: type_impls */
typedef struct
g0_istruct_prod
{
  MDArr g0_member1_pair;
  MDArr g0_member2_pair;
} pair_MDArr_MDArr;

typedef struct
g1_istruct_prod
{
  MDArr g1_member1_pair;
  nat g1_member2_pair;
} pair_MDArr_nat;

typedef struct
g2_istruct_prod
{
  pair_MDArr_MDArr g2_member1_pair;
  nat g2_member2_pair;
} pair_2MDArr_nat;

struct g3_istruct_Aux
{
  bool g3_member1_mkAux_query_bit;
  bits g3_member2_mkAux_input_bits;
  nat g3_member3_mkAux_ratio;
  nat g3_member4_mkAux_blksz2;
  DArr g3_member5_mkAux_dir1;
  DArr g3_member6_mkAux_dir2;
};

/* section-end: type_impls */
/* section-start: func_decls */
static MDArr pair_MDArr_MDArr_D1(pair_MDArr_MDArr x);
static MDArr pair_MDArr_MDArr_D2(pair_MDArr_MDArr x);
static pair_MDArr_MDArr make_pair_MDArr_MDArr(MDArr g0_member1_pair,
  MDArr g0_member2_pair);

static MDArr pair_MDArr_nat_D(pair_MDArr_nat x);
static nat pair_MDArr_nat_n(pair_MDArr_nat x);
static pair_MDArr_nat make_pair_MDArr_nat(MDArr g1_member1_pair,
  nat g1_member2_pair);

static pair_MDArr_MDArr pair_2MDArr_nat_D12(pair_2MDArr_nat x);
static nat pair_2MDArr_nat_n(pair_2MDArr_nat x);
static pair_2MDArr_nat make_pair_2MDArr_nat(pair_MDArr_MDArr g2_member1_pair,
  nat g2_member2_pair);

static bool aux_query_bit(Aux x);
static bits aux_input_bits(Aux x);
static nat aux_blksz2(Aux x);
static nat aux_ratio(Aux x);
static DArr aux_dir1(Aux x);
static DArr aux_dir2(Aux x);
static Aux mkAux(bool g3_member1_mkAux_query_bit,
  bits g3_member2_mkAux_input_bits, nat g3_member3_mkAux_ratio,
  nat g3_member4_mkAux_blksz2, DArr g3_member5_mkAux_dir1,
  DArr g3_member6_mkAux_dir2);

/* section-end: func_decls */
/* section-start: func_impls */
static MDArr pair_MDArr_MDArr_D1(pair_MDArr_MDArr x)
{
  return x.g0_member1_pair;
}
static MDArr pair_MDArr_MDArr_D2(pair_MDArr_MDArr x)
{
  return x.g0_member2_pair;
}
static pair_MDArr_MDArr make_pair_MDArr_MDArr(MDArr g0_member1_pair,
  MDArr g0_member2_pair)
{
  pair_MDArr_MDArr ret = { g0_member1_pair, g0_member2_pair };
  return ret;
}

static MDArr pair_MDArr_nat_D(pair_MDArr_nat x)
{
  return x.g1_member1_pair;
}
static nat pair_MDArr_nat_n(pair_MDArr_nat x)
{
  return x.g1_member2_pair;
}
static pair_MDArr_nat make_pair_MDArr_nat(MDArr g1_member1_pair,
  nat g1_member2_pair)
{
  pair_MDArr_nat ret = { g1_member1_pair, g1_member2_pair };
  return ret;
}

static pair_MDArr_MDArr pair_2MDArr_nat_D12(pair_2MDArr_nat x)
{
  return x.g2_member1_pair;
}
static nat pair_2MDArr_nat_n(pair_2MDArr_nat x)
{
  return x.g2_member2_pair;
}
static pair_2MDArr_nat make_pair_2MDArr_nat(pair_MDArr_MDArr g2_member1_pair,
  nat g2_member2_pair)
{
  pair_2MDArr_nat ret = { g2_member1_pair, g2_member2_pair };
  return ret;
}

static bool aux_query_bit(Aux x)
{
  return (x->g3_member1_mkAux_query_bit);
}
static bits aux_input_bits(Aux x)
{
  return (x->g3_member2_mkAux_input_bits);
}
static nat aux_blksz2(Aux x)
{
  return (x->g3_member3_mkAux_ratio);
}
static nat aux_ratio(Aux x)
{
  return (x->g3_member4_mkAux_blksz2);
}
static DArr aux_dir1(Aux x)
{
  return (x->g3_member5_mkAux_dir1);
}
static DArr aux_dir2(Aux x)
{
  return (x->g3_member6_mkAux_dir2);
}
static Aux mkAux(bool g3_member1_mkAux_query_bit,
  bits g3_member2_mkAux_input_bits, nat g3_member3_mkAux_ratio,
  nat g3_member4_mkAux_blksz2, DArr g3_member5_mkAux_dir1,
  DArr g3_member6_mkAux_dir2)
{
  Aux p;
  if (!(p = malloc(sizeof(*p)))) abort();
  p->g3_member1_mkAux_query_bit = g3_member1_mkAux_query_bit;
  p->g3_member2_mkAux_input_bits = g3_member2_mkAux_input_bits;
  p->g3_member3_mkAux_ratio = g3_member3_mkAux_ratio;
  p->g3_member4_mkAux_blksz2 = g3_member4_mkAux_blksz2;
  p->g3_member5_mkAux_dir1 = g3_member5_mkAux_dir1;
  p->g3_member6_mkAux_dir2 = g3_member6_mkAux_dir2;
  return p;
}



static pair_MDArr_nat
buildDir2(bool v1_b, bits v2_s, nat v3_sz2, nat v4_c, nat v5_i, MDArr v6_D2,
         nat v7_m2)
{
  nat v8_cp;
  nat v9_m;
  nat v10_n;
  MDArr v11_m;
  nat v12_n;
  entry_buildDir2:
  switch (v4_c)
  {
    case 0:
      return make_pair_MDArr_nat(v6_D2, v7_m2);
    default:
      v8_cp = predn(v4_c);
      v9_m = bcount(v1_b, v5_i, v3_sz2, v2_s);
      v10_n = addn(v5_i, v3_sz2);
      v11_m = pushD(v6_D2, v7_m2);
      v12_n = addn(v7_m2, v9_m);
      v4_c = v8_cp;
      v5_i = v10_n;
      v6_D2 = v11_m;
      v7_m2 = v12_n;
      goto entry_buildDir2;
  }
}




static pair_2MDArr_nat
buildDir1(bool v1_b, bits v2_s, nat v3_k, nat v4_sz1, nat v5_sz2, nat v6_c,
         nat v7_i, MDArr v8_D1, MDArr v9_D2, nat v10_m1)
{
  pair_MDArr_MDArr v11_p;
  nat v12_cp;
  MDArr v13_D1_;
  nat v14_n;
  pair_MDArr_nat v15_p;
  MDArr v16_D2_;
  nat v17_m2;
  nat v18_n;
  nat v19_n;
  entry_buildDir1:
  switch (v6_c)
  {
    case 0:
      v11_p = make_pair_MDArr_MDArr(v8_D1, v9_D2);
      return make_pair_2MDArr_nat(v11_p, v10_m1);
    default:
      v12_cp = predn(v6_c);
      v13_D1_ = pushD(v8_D1, v10_m1);
      v14_n = 0;
      v15_p = buildDir2(v1_b, v2_s, v5_sz2, v3_k, v7_i, v9_D2, v14_n);
      v16_D2_ = pair_MDArr_nat_D(v15_p);
      v17_m2 = pair_MDArr_nat_n(v15_p);
      v18_n = addn(v7_i, v4_sz1);
      v19_n = addn(v10_m1, v17_m2);
      v6_c = v12_cp;
      v7_i = v18_n;
      v8_D1 = v13_D1_;
      v9_D2 = v16_D2_;
      v10_m1 = v19_n;
      goto entry_buildDir1;
  }
}




static pair_MDArr_MDArr
buildDir(bool v1_b, bits v2_s, nat v3_k, nat v4_sz2, nat v5_w1, nat v6_w2)
{
  nat v7_sz1;
  nat v8_n;
  nat v9_n2;
  nat v10_n1;
  nat v11_n;
  MDArr v12_m;
  MDArr v13_m;
  nat v14_n;
  pair_2MDArr_nat v15_p;
  pair_MDArr_MDArr v16_p;
  nat v17_m1;
  MDArr v18_D1;
  MDArr v19_D2;
  nat v20_n;
  nat v21_n;
  nat v22_n;
  pair_MDArr_nat v23_p;
  MDArr v24_D2;
  nat v25_m2;
  MDArr v26_m;
  MDArr v27_m;
  v7_sz1 = muln(v3_k, v4_sz2);
  v8_n = bsize(v2_s);
  v9_n2 = divn(v8_n, v4_sz2);
  v10_n1 = divn(v9_n2, v3_k);
  v11_n = 0;
  v12_m = emptyD(v5_w1);
  v13_m = emptyD(v6_w2);
  v14_n = 0;
  v15_p = buildDir1(v1_b, v2_s, v3_k, v7_sz1, v4_sz2, v10_n1, v11_n, v12_m,
  v13_m, v14_n);
  v16_p = pair_2MDArr_nat_D12(v15_p);
  v17_m1 = pair_2MDArr_nat_n(v15_p);
  v18_D1 = pair_MDArr_MDArr_D1(v16_p);
  v19_D2 = pair_MDArr_MDArr_D2(v16_p);
  v20_n = modn(v9_n2, v3_k);
  v21_n = muln(v10_n1, v7_sz1);
  v22_n = 0;
  v23_p = buildDir2(v1_b, v2_s, v4_sz2, v20_n, v21_n, v19_D2, v22_n);
  v24_D2 = pair_MDArr_nat_D(v23_p);
  v25_m2 = pair_MDArr_nat_n(v23_p);
  v26_m = pushD(v18_D1, v17_m1);
  v27_m = pushD(v24_D2, v25_m2);
  return make_pair_MDArr_MDArr(v26_m, v27_m);
}




static nat pred(nat v1_n)
{
  nat v2_u;
  switch (v1_n)
  {
    case 0:
      return v1_n;
    default:
      v2_u = predn(v1_n);
      return v2_u;
  }
}




static nat neq0(nat v1_n)
{
  nat v2_n;
  v2_n = pred(v1_n);
  return succn(v2_n);
}




static Aux rank_init(bool v1_b, bits v2_s)
{
  nat v3_n;
  nat v4_kp;
  nat v5_k;
  nat v6_sz2p;
  nat v7_sz2;
  nat v8_sz1;
  nat v9_n;
  nat v10_n;
  nat v11_n;
  nat v12_w1;
  nat v13_n;
  nat v14_n;
  nat v15_w2;
  pair_MDArr_MDArr v16_p;
  MDArr v17_D1;
  MDArr v18_D2;
  DArr v19_d;
  DArr v20_d;
  v3_n = bsize(v2_s);
  v4_kp = bitlen(v3_n);
  v5_k = succn(v4_kp);
  v6_sz2p = bitlen(v3_n);
  v7_sz2 = succn(v6_sz2p);
  v8_sz1 = muln(v5_k, v7_sz2);
  v9_n = divn(v3_n, v8_sz1);
  v10_n = muln(v9_n, v8_sz1);
  v11_n = bitlen(v10_n);
  v12_w1 = neq0(v11_n);
  v13_n = muln(v4_kp, v7_sz2);
  v14_n = bitlen(v13_n);
  v15_w2 = neq0(v14_n);
  v16_p = buildDir(v1_b, v2_s, v5_k, v7_sz2, v12_w1, v15_w2);
  v17_D1 = pair_MDArr_MDArr_D1(v16_p);
  v18_D2 = pair_MDArr_MDArr_D2(v16_p);
  v19_d = freezeD(v17_D1);
  v20_d = freezeD(v18_D2);
  return mkAux(v1_b, v2_s, v5_k, v7_sz2, v19_d, v20_d);
}




static nat rank_lookup(Aux v1_aux, nat v2_i)
{
  bool v3_b;
  bits v4_s;
  nat v5_k;
  nat v6_sz2;
  DArr v7_D1;
  DArr v8_D2;
  nat v9_j2;
  nat v10_j3;
  nat v11_j1;
  nat v12_n;
  nat v13_n;
  nat v14_n;
  nat v15_n;
  nat v16_n;
  v3_b = aux_query_bit(v1_aux);
  v4_s = aux_input_bits(v1_aux);
  v5_k = aux_ratio(v1_aux);
  v6_sz2 = aux_blksz2(v1_aux);
  v7_D1 = aux_dir1(v1_aux);
  v8_D2 = aux_dir2(v1_aux);
  v9_j2 = divn(v2_i, v6_sz2);
  v10_j3 = modn(v2_i, v6_sz2);
  v11_j1 = divn(v9_j2, v5_k);
  v12_n = lookupD(v7_D1, v11_j1);
  v13_n = lookupD(v8_D2, v9_j2);
  v14_n = addn(v12_n, v13_n);
  v15_n = muln(v9_j2, v6_sz2);
  v16_n = bcount(v3_b, v15_n, v10_j3, v4_s);
  return addn(v14_n, v16_n);
}


/* section-end: func_impls */
/* section-start: epilogue */
/* section-end: epilogue */
