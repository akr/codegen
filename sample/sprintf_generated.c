/* section-start: prologue */
/* section-end: prologue */
/* section-start: type_decls */
/* section-end: type_decls */
/* section-start: type_impls */
/* section-end: type_impls */
/* section-start: func_decls */
/* section-end: func_decls */
/* section-start: func_impls */


static buffer codegen_p0_sprintf(buffer v1_buf, nat v2_n, nat v3_n, nat v4_n)
{
  bool v5_b;
  bool v6_b;
  bool v7_b;
  bool v8_b;
  bool v9_b;
  bool v10_b;
  bool v11_b;
  bool v12_b;
  unsigned char v13_a;
  bool v14_b;
  bool v15_b;
  bool v16_b;
  bool v17_b;
  bool v18_b;
  bool v19_b;
  bool v20_b;
  bool v21_b;
  unsigned char v22_a;
  bool v23_b;
  bool v24_b;
  bool v25_b;
  bool v26_b;
  bool v27_b;
  bool v28_b;
  bool v29_b;
  bool v30_b;
  unsigned char v31_a;
  bool v32_b;
  bool v33_b;
  bool v34_b;
  bool v35_b;
  bool v36_b;
  bool v37_b;
  bool v38_b;
  bool v39_b;
  unsigned char v40_a;
  bool v41_b;
  bool v42_b;
  bool v43_b;
  bool v44_b;
  bool v45_b;
  bool v46_b;
  bool v47_b;
  bool v48_b;
  unsigned char v49_a;
  bool v50_b;
  bool v51_b;
  bool v52_b;
  bool v53_b;
  bool v54_b;
  bool v55_b;
  bool v56_b;
  bool v57_b;
  unsigned char v58_a;
  bool v59_b;
  bool v60_b;
  bool v61_b;
  bool v62_b;
  bool v63_b;
  bool v64_b;
  bool v65_b;
  bool v66_b;
  unsigned char v67_a;
  buffer v68_b;
  buffer v69_b;
  buffer v70_b;
  buffer v71_b;
  buffer v72_b;
  buffer v73_b;
  buffer v74_b;
  buffer v75_b;
  buffer v76_b;
  buffer v77_b;
  v5_b = false;
  v6_b = false;
  v7_b = false;
  v8_b = false;
  v9_b = false;
  v10_b = true;
  v11_b = false;
  v12_b = false;
  v13_a = make_char(v5_b, v6_b, v7_b, v8_b, v9_b, v10_b, v11_b, v12_b);
  v14_b = true;
  v15_b = true;
  v16_b = false;
  v17_b = true;
  v18_b = false;
  v19_b = true;
  v20_b = false;
  v21_b = false;
  v22_a = make_char(v14_b, v15_b, v16_b, v17_b, v18_b, v19_b, v20_b, v21_b);
  v23_b = false;
  v24_b = false;
  v25_b = false;
  v26_b = false;
  v27_b = false;
  v28_b = true;
  v29_b = false;
  v30_b = false;
  v31_a = make_char(v23_b, v24_b, v25_b, v26_b, v27_b, v28_b, v29_b, v30_b);
  v32_b = false;
  v33_b = false;
  v34_b = false;
  v35_b = false;
  v36_b = false;
  v37_b = true;
  v38_b = false;
  v39_b = false;
  v40_a = make_char(v32_b, v33_b, v34_b, v35_b, v36_b, v37_b, v38_b, v39_b);
  v41_b = true;
  v42_b = false;
  v43_b = false;
  v44_b = true;
  v45_b = false;
  v46_b = true;
  v47_b = true;
  v48_b = false;
  v49_a = make_char(v41_b, v42_b, v43_b, v44_b, v45_b, v46_b, v47_b, v48_b);
  v50_b = true;
  v51_b = true;
  v52_b = false;
  v53_b = false;
  v54_b = true;
  v55_b = true;
  v56_b = true;
  v57_b = false;
  v58_a = make_char(v50_b, v51_b, v52_b, v53_b, v54_b, v55_b, v56_b, v57_b);
  v59_b = false;
  v60_b = false;
  v61_b = false;
  v62_b = false;
  v63_b = false;
  v64_b = true;
  v65_b = false;
  v66_b = false;
  v67_a = make_char(v59_b, v60_b, v61_b, v62_b, v63_b, v64_b, v65_b, v66_b);
  v68_b = buf_addnat(v1_buf, v2_n);
  v69_b = buf_addch(v68_b, v13_a);
  v70_b = buf_addch(v69_b, v22_a);
  v71_b = buf_addch(v70_b, v31_a);
  v72_b = buf_addnat(v71_b, v3_n);
  v73_b = buf_addch(v72_b, v40_a);
  v74_b = buf_addch(v73_b, v49_a);
  v75_b = buf_addch(v74_b, v58_a);
  v76_b = buf_addch(v75_b, v67_a);
  v77_b = buf_addnat(v76_b, v4_n);
  return v77_b;
}




static buffer add_mesg(nat v1_a, nat v2_b)
{
  nat v3_n;
  buffer v4_b;
  nat v5_n;
  v3_n = 0;
  v4_b = make_buffer(v3_n);
  v5_n = nat_add(v1_a, v2_b);
  return codegen_p0_sprintf(v4_b, v1_a, v2_b, v5_n);
}


/* section-end: func_impls */
/* section-start: epilogue */
/* section-end: epilogue */
