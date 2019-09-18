nat
n3_fastpow_iter(nat v0_a, nat v1_k, nat v2_x)
{
  n3_fastpow_iter:;
  switch (sw_nat(v1_k))
  {
    case_O_nat: { return v2_x; }
    case_S_nat: {
      nat v3_k_ = field0_S_nat(v1_k);
      bool v4_b = n1_odd(v1_k);
      switch (sw_bool(v4_b))
      {
        case_true_bool: {
          nat v5_n = n2_muln(v0_a, v2_x);
          v1_k = v3_k_;
          v2_x = v5_n;
          goto n3_fastpow_iter;
        }
        case_false_bool: {
          nat v6_n = n2_muln(v0_a, v0_a);
          nat v7_n = n1_uphalf_(v3_k_);
          v0_a = v6_n;
          v1_k = v7_n;
          goto n3_fastpow_iter;
        }
      }
    }
  }
}
nat
n2_fastpow(nat v0_a, nat v1_k)
{
  nat v2_n = n0_O();
  nat v3_n = n1_S(v2_n);
  return n3_fastpow_iter(v0_a, v1_k, v3_n);
}
