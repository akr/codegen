nat
n3_fastpow_iter(nat v2_a, nat v1_k, nat v0_x)
{
  n3_fastpow_iter:;
  switch (sw_nat(v1_k))
  {
    case_O_nat: { return v0_x; }
    case_S_nat: {
      nat v4_k_ = field0_S_nat(v1_k);
      bool v5_b = n1_odd(v1_k);
      switch (sw_bool(v5_b))
      {
        case_true_bool: {
          nat v6_n = n2_muln(v2_a, v0_x);
          v1_k = v4_k_;
          v0_x = v6_n;
          goto n3_fastpow_iter;
        }
        case_false_bool: {
          nat v7_n = n2_muln(v2_a, v2_a);
          nat v8_n = n1_uphalf_(v4_k_);
          v2_a = v7_n;
          v1_k = v8_n;
          goto n3_fastpow_iter;
        }
      }
    }
  }
}
nat
n2_fastpow(nat v10_a, nat v9_k)
{
  nat v11_n = n0_O();
  nat v12_n = n1_S(v11_n);
  return n3_fastpow_iter(v10_a, v9_k, v12_n);
}
