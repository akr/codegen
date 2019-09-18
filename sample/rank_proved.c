nat
n1_pred(nat v0_n)
{
  switch (sw_nat(v0_n))
  {
    case_O_nat: { return v0_n; }
    case_S_nat: { nat v1_u = field0_S_nat(v0_n); return v1_u; }
  }
}
nat n1_neq0(nat v0_n) { nat v1_n = n1_pred(v0_n); return n1_S(v1_n); }
prod_MDArr_nat
n7_buildDir2(bool v0_b,
             bits v1_s,
             nat v2_sz2,
             nat v3_c,
             nat v4_i,
             MDArr v5_D2,
             nat v6_m2)
{
  n7_buildDir2:;
  switch (sw_nat(v3_c))
  {
    case_O_nat: { return n2_pair_MDArr_nat(v5_D2, v6_m2); }
    case_S_nat: {
      nat v7_cp = field0_S_nat(v3_c);
      nat v8_m = n4_bcount(v0_b, v4_i, v2_sz2, v1_s);
      nat v9_n = n2_addn(v4_i, v2_sz2);
      MDArr v10_m = n2_pushD(v5_D2, v6_m2);
      nat v11_n = n2_addn(v6_m2, v8_m);
      v3_c = v7_cp;
      v4_i = v9_n;
      v5_D2 = v10_m;
      v6_m2 = v11_n;
      goto n7_buildDir2;
    }
  }
}
prod_prod_MDArr_MDArr_nat
n10_buildDir1(bool v0_b,
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
  n10_buildDir1:;
  switch (sw_nat(v5_c))
  {
    case_O_nat: {
      prod_MDArr_MDArr v10_p = n2_pair_MDArr_MDArr(v7_D1, v8_D2);
      return n2_pair_prod_MDArr_MDArr_nat(v10_p, v9_m1);
    }
    case_S_nat: {
      nat v11_cp = field0_S_nat(v5_c);
      MDArr v12_D1_ = n2_pushD(v7_D1, v9_m1);
      nat v13_n = n0_O();
      prod_MDArr_nat
      v14_p
      =
      n7_buildDir2(v0_b,
      v1_s,
      v4_sz2,
      v2_k,
      v6_i,
      v8_D2,
      v13_n);
      MDArr v15_D2_ = field0_pair_prod_MDArr_nat(v14_p);
      nat v16_m2 = field1_pair_prod_MDArr_nat(v14_p);
      nat v17_n = n2_addn(v6_i, v3_sz1);
      nat v18_n = n2_addn(v9_m1, v16_m2);
      v5_c = v11_cp;
      v6_i = v17_n;
      v7_D1 = v12_D1_;
      v8_D2 = v15_D2_;
      v9_m1 = v18_n;
      goto n10_buildDir1;
    }
  }
}
prod_MDArr_MDArr
n6_buildDir(bool v0_b, bits v1_s, nat v2_k, nat v3_sz2, nat v4_w1, nat v5_w2)
{
  nat v6_sz1 = n2_muln(v2_k, v3_sz2);
  nat v7_n = n1_bsize(v1_s);
  nat v8_n2 = n2_divn(v7_n, v3_sz2);
  nat v9_n1 = n2_divn(v8_n2, v2_k);
  nat v10_n = n0_O();
  MDArr v11_m = n1_emptyD(v4_w1);
  MDArr v12_m = n1_emptyD(v5_w2);
  nat v13_n = n0_O();
  prod_prod_MDArr_MDArr_nat
  v14_p
  =
  n10_buildDir1(v0_b,
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
  nat v19_n = n2_modn(v8_n2, v2_k);
  nat v20_n = n2_muln(v9_n1, v6_sz1);
  nat v21_n = n0_O();
  prod_MDArr_nat
  v22_p
  =
  n7_buildDir2(v0_b,
  v1_s,
  v3_sz2,
  v19_n,
  v20_n,
  v18_D2,
  v21_n);
  MDArr v23_D2 = field0_pair_prod_MDArr_nat(v22_p);
  nat v24_m2 = field1_pair_prod_MDArr_nat(v22_p);
  MDArr v25_m = n2_pushD(v17_D1, v16_m1);
  MDArr v26_m = n2_pushD(v23_D2, v24_m2);
  return n2_pair_MDArr_MDArr(v25_m, v26_m);
}
Aux
n2_rank_init(bool v0_b, bits v1_s)
{
  nat v2_n = n1_bsize(v1_s);
  nat v3_kp = n1_bitlen(v2_n);
  nat v4_k = n1_S(v3_kp);
  nat v5_sz2p = n1_bitlen(v2_n);
  nat v6_sz2 = n1_S(v5_sz2p);
  nat v7_sz1 = n2_muln(v4_k, v6_sz2);
  nat v8_n = n2_divn(v2_n, v7_sz1);
  nat v9_n = n2_muln(v8_n, v7_sz1);
  nat v10_n = n1_bitlen(v9_n);
  nat v11_w1 = n1_neq0(v10_n);
  nat v12_n = n2_muln(v3_kp, v6_sz2);
  nat v13_n = n1_bitlen(v12_n);
  nat v14_w2 = n1_neq0(v13_n);
  prod_MDArr_MDArr
  v15_p
  =
  n6_buildDir(v0_b,
  v1_s,
  v4_k,
  v6_sz2,
  v11_w1,
  v14_w2);
  MDArr v16_D1 = field0_pair_prod_MDArr_MDArr(v15_p);
  MDArr v17_D2 = field1_pair_prod_MDArr_MDArr(v15_p);
  DArr v18_d = n1_freezeD(v16_D1);
  DArr v19_d = n1_freezeD(v17_D2);
  return n6_mkAux(v0_b, v1_s, v4_k, v6_sz2, v18_d, v19_d);
}
nat
n2_rank_lookup(Aux v0_aux, nat v1_i)
{
  bool v2_b = n1_query_bit(v0_aux);
  bits v3_s = n1_input_bits(v0_aux);
  nat v4_k = n1_ratio(v0_aux);
  nat v5_sz2 = n1_blksz2(v0_aux);
  DArr v6_D1 = n1_dir1(v0_aux);
  DArr v7_D2 = n1_dir2(v0_aux);
  nat v8_j2 = n2_divn(v1_i, v5_sz2);
  nat v9_j3 = n2_modn(v1_i, v5_sz2);
  nat v10_j1 = n2_divn(v8_j2, v4_k);
  nat v11_n = n2_lookupD(v6_D1, v10_j1);
  nat v12_n = n2_lookupD(v7_D2, v8_j2);
  nat v13_n = n2_addn(v11_n, v12_n);
  nat v14_n = n2_muln(v8_j2, v5_sz2);
  nat v15_n = n4_bcount(v2_b, v14_n, v9_j3, v3_s);
  return n2_addn(v13_n, v15_n);
}
