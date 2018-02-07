nat
n1_pred(nat v0_n)
{
  switch (sw_nat(v0_n))
  {
    case_O_nat: { return v0_n; }
    case_S_nat: { nat v1_u = field0_S_nat(v0_n); return v1_u; }
  }
}
nat n1_neq0(nat v2_n) { nat v3_n = n1_pred(v2_n); return n1_S(v3_n); }
prod_MDArr_nat
n7_buildDir2(bool v10_b,
             bits v9_s,
             nat v8_sz2,
             nat v7_c,
             nat v6_i,
             MDArr v5_D2,
             nat v4_m2)
{
  n7_buildDir2:;
  switch (sw_nat(v7_c))
  {
    case_O_nat: { return n2_pair_MDArr_nat(v5_D2, v4_m2); }
    case_S_nat: {
      nat v12_cp = field0_S_nat(v7_c);
      nat v13_m = n4_bcount(v10_b, v6_i, v8_sz2, v9_s);
      nat v14_n = n2_addn(v6_i, v8_sz2);
      MDArr v15_m = n2_pushD(v5_D2, v4_m2);
      nat v16_n = n2_addn(v4_m2, v13_m);
      v7_c = v12_cp;
      v6_i = v14_n;
      v5_D2 = v15_m;
      v4_m2 = v16_n;
      goto n7_buildDir2;
    }
  }
}
prod_prod_MDArr_MDArr_nat
n10_buildDir1(bool v26_b,
              bits v25_s,
              nat v24_k,
              nat v23_sz1,
              nat v22_sz2,
              nat v21_c,
              nat v20_i,
              MDArr v19_D1,
              MDArr v18_D2,
              nat v17_m1)
{
  n10_buildDir1:;
  switch (sw_nat(v21_c))
  {
    case_O_nat: {
      prod_MDArr_MDArr v28_p = n2_pair_MDArr_MDArr(v19_D1, v18_D2);
      return n2_pair_prod_MDArr_MDArr_nat(v28_p, v17_m1);
    }
    case_S_nat: {
      nat v29_cp = field0_S_nat(v21_c);
      MDArr v30_D1_ = n2_pushD(v19_D1, v17_m1);
      nat v31_n = n0_O();
      prod_MDArr_nat
      v32_p
      =
      n7_buildDir2(v26_b,
      v25_s,
      v22_sz2,
      v24_k,
      v20_i,
      v18_D2,
      v31_n);
      MDArr v33_D2_ = field0_pair_prod_MDArr_nat(v32_p);
      nat v34_m2 = field1_pair_prod_MDArr_nat(v32_p);
      nat v35_n = n2_addn(v20_i, v23_sz1);
      nat v36_n = n2_addn(v17_m1, v34_m2);
      v21_c = v29_cp;
      v20_i = v35_n;
      v19_D1 = v30_D1_;
      v18_D2 = v33_D2_;
      v17_m1 = v36_n;
      goto n10_buildDir1;
    }
  }
}
prod_MDArr_MDArr
n6_buildDir(bool v42_b,
            bits v41_s,
            nat v40_k,
            nat v39_sz2,
            nat v38_w1,
            nat v37_w2)
{
  nat v43_sz1 = n2_muln(v40_k, v39_sz2);
  nat v44_n = n1_bsize(v41_s);
  nat v45_n2 = n2_divn(v44_n, v39_sz2);
  nat v46_n1 = n2_divn(v45_n2, v40_k);
  nat v47_n = n0_O();
  MDArr v48_m = n1_emptyD(v38_w1);
  MDArr v49_m = n1_emptyD(v37_w2);
  nat v50_n = n0_O();
  prod_prod_MDArr_MDArr_nat
  v51_p
  =
  n10_buildDir1(v42_b,
  v41_s,
  v40_k,
  v43_sz1,
  v39_sz2,
  v46_n1,
  v47_n,
  v48_m,
  v49_m,
  v50_n);
  prod_MDArr_MDArr v52_p = field0_pair_prod_prod_MDArr_MDArr_nat(v51_p);
  nat v53_m1 = field1_pair_prod_prod_MDArr_MDArr_nat(v51_p);
  MDArr v54_D1 = field0_pair_prod_MDArr_MDArr(v52_p);
  MDArr v55_D2 = field1_pair_prod_MDArr_MDArr(v52_p);
  nat v56_n = n2_modn(v45_n2, v40_k);
  nat v57_n = n2_muln(v46_n1, v43_sz1);
  nat v58_n = n0_O();
  prod_MDArr_nat
  v59_p
  =
  n7_buildDir2(v42_b,
  v41_s,
  v39_sz2,
  v56_n,
  v57_n,
  v55_D2,
  v58_n);
  MDArr v60_D2 = field0_pair_prod_MDArr_nat(v59_p);
  nat v61_m2 = field1_pair_prod_MDArr_nat(v59_p);
  MDArr v62_m = n2_pushD(v54_D1, v53_m1);
  MDArr v63_m = n2_pushD(v60_D2, v61_m2);
  return n2_pair_MDArr_MDArr(v62_m, v63_m);
}
Aux
n2_rank_init(bool v65_b, bits v64_s)
{
  nat v66_n = n1_bsize(v64_s);
  nat v67_kp = n1_bitlen(v66_n);
  nat v68_k = n1_S(v67_kp);
  nat v69_sz2p = n1_bitlen(v66_n);
  nat v70_sz2 = n1_S(v69_sz2p);
  nat v71_sz1 = n2_muln(v68_k, v70_sz2);
  nat v72_n = n2_divn(v66_n, v71_sz1);
  nat v73_n = n2_muln(v72_n, v71_sz1);
  nat v74_n = n1_bitlen(v73_n);
  nat v75_w1 = n1_neq0(v74_n);
  nat v76_n = n2_muln(v67_kp, v70_sz2);
  nat v77_n = n1_bitlen(v76_n);
  nat v78_w2 = n1_neq0(v77_n);
  prod_MDArr_MDArr
  v79_p
  =
  n6_buildDir(v65_b,
  v64_s,
  v68_k,
  v70_sz2,
  v75_w1,
  v78_w2);
  MDArr v80_D1 = field0_pair_prod_MDArr_MDArr(v79_p);
  MDArr v81_D2 = field1_pair_prod_MDArr_MDArr(v79_p);
  DArr v82_d = n1_freezeD(v80_D1);
  DArr v83_d = n1_freezeD(v81_D2);
  return n6_mkAux(v65_b, v64_s, v68_k, v70_sz2, v82_d, v83_d);
}
nat
n2_rank_lookup(Aux v85_aux, nat v84_i)
{
  bool v86_b = n1_query_bit(v85_aux);
  bits v87_s = n1_input_bits(v85_aux);
  nat v88_k = n1_ratio(v85_aux);
  nat v89_sz2 = n1_blksz2(v85_aux);
  DArr v90_D1 = n1_dir1(v85_aux);
  DArr v91_D2 = n1_dir2(v85_aux);
  nat v92_j2 = n2_divn(v84_i, v89_sz2);
  nat v93_j3 = n2_modn(v84_i, v89_sz2);
  nat v94_j1 = n2_divn(v92_j2, v88_k);
  nat v95_n = n2_lookupD(v90_D1, v94_j1);
  nat v96_n = n2_lookupD(v91_D2, v92_j2);
  nat v97_n = n2_addn(v95_n, v96_n);
  nat v98_n = n2_muln(v92_j2, v89_sz2);
  nat v99_n = n4_bcount(v86_b, v98_n, v93_j3, v87_s);
  return n2_addn(v97_n, v99_n);
}
