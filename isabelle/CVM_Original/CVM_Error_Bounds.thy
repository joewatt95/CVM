theory CVM_Error_Bounds

imports
  CVM_Algo_Nondet_Binomial

begin

locale cvm_error_bounds = cvm_algo + fixes
  r l :: nat and
  \<epsilon> :: real and
  xs :: \<open>'a list\<close>
begin

abbreviation
  \<open>run_with_bernoulli_matrix \<equiv> \<lambda> g.
    map_pmf (g xs) (bernoulli_matrix (length xs) (length xs) f)\<close>

text \<open>Bound for the case when k <= l\<close>
definition
  \<open>prob_k_le_l_and_est_out_of_range_bound \<equiv>
    4 * exp (-\<epsilon>\<^sup>2 * threshold / (4 * real r * (1 + \<epsilon> / 3)))\<close>

text \<open>Bound for the case when k > l\<close>
definition
  \<open>prob_k_gt_l_bound \<equiv>
    real (length xs) *
    exp (-3 * real threshold * (r - 1)\<^sup>2 / (5 * r + 2 * r\<^sup>2))\<close>

end

locale cvm_error_bounds_assms = cvm_error_bounds + cvm_algo_assms
begin

subsection \<open>Proof for k <= l case.\<close>

context
  assumes
    \<open>threshold \<ge> r\<close>
    \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close>
begin

lemma l_le_length_xs :
  \<open>l \<le> length xs\<close>
proof -
  from \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close>
  have \<open>l \<le> floor_log (2 * r * card (set xs) div threshold)\<close>
    by (metis floor_log_le_iff less_eq_div_iff_mult_less_eq floor_log_power threshold)

  also from \<open>threshold \<ge> r\<close>
  have \<open>\<dots> \<le> floor_log (2 * length xs)\<close>
    apply (intro floor_log_le_iff)
    by (metis card_length cross3_simps(12) div_le_mono div_mult_self1_is_m more_arith_simps(11) mult_le_mono mult_le_mono2 threshold)

  also have \<open>\<dots> \<le> length xs\<close>
    by (metis floor_log_le_iff less_exp floor_log_exp2_le floor_log_power floor_log_twice nat_0_less_mult_iff not_le not_less_eq_eq order_class.order_eq_iff self_le_ge2_pow zero_le)

  finally show ?thesis .
qed

lemma r_pos :
  \<open>r > 0\<close>
  using
    \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close> threshold power_eq_0_iff
  by fastforce

subsection \<open>Proof for k > l case.\<close>

end

end