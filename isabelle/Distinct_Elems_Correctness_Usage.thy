theory Distinct_Elems_Correctness_Usage

imports
  "HOL-Decision_Procs.Approximation"
  CVM.Distinct_Elems_Correctness

begin

context
  fixes
    \<epsilon> \<delta> :: real and
    xs :: \<open>'a list\<close>
  assumes \<epsilon> : \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> and \<delta> : \<open>0 < \<delta>\<close> \<open>\<delta> \<le> 1\<close>
begin

definition \<open>threshold \<equiv> 12 * log 2 (8 * real (max 1 <| length xs) / \<delta>) / \<epsilon>\<^sup>2\<close>

definition \<open>l \<equiv> \<lfloor>log 2 <| 4 * card (set xs) / \<lceil>threshold\<rceil>\<rfloor>\<close>

context
  assumes
    \<open>xs \<noteq> []\<close>
    \<open>threshold \<le> card (set xs)\<close>
begin

lemma threshold_ge_2 :
  \<open>threshold \<ge> 2\<close>
  using \<epsilon> \<delta> \<open>xs \<noteq> []\<close>
  apply (simp add: threshold_def log_divide log_mult nonempty_iff_length_ge_1 field_simps)
  by (smt (verit, best) log_le_one_cancel_iff log_le_zero_cancel_iff log_less_zero_cancel_iff numeral_nat(7) one_of_nat_le_iff power_le_one) 

lemma \<epsilon>_threshold_ge_12 :
  \<open>\<epsilon>\<^sup>2 * threshold \<ge> 12\<close> (is ?thesis_0) 
  \<open>\<epsilon>\<^sup>2 * \<lceil>threshold\<rceil> \<ge> 12\<close> (is ?thesis_1) 
proof -
  from \<epsilon> \<delta> \<open>xs \<noteq> []\<close>
  show ?thesis_0
    by (simp add: threshold_def nonempty_iff_length_ge_1 field_simps)

  with \<epsilon> show ?thesis_1
    by (meson landau_omega.R_mult_left_mono le_of_int_ceiling order_trans_rules(23) zero_compare_simps(12))
qed

lemma l_pos : \<open>l > 0\<close>
  using \<open>threshold \<le> card (set xs)\<close> threshold_ge_2
  apply (simp add: l_def field_simps)
  by linarith

lemma two_l_threshold_bounds :
  defines [simp] : \<open>two_l_threshold \<equiv> 2 ^ nat l * nat \<lceil>threshold\<rceil>\<close>
  shows
    \<open>2 * card (set xs) \<le> two_l_threshold\<close> (is \<open>?lower \<le> _\<close>)
    \<open>two_l_threshold \<le> 4 * card (set xs)\<close> (is \<open>_ \<le> ?upper\<close>)
proof -
  from \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close> l_pos threshold_ge_2
  have \<open>log 2 ?lower \<le> log 2 two_l_threshold\<close>
    apply (simp add: l_def log_mult log_divide field_simps split: if_splits)
    by (smt (z3) Num.of_nat_simps(2,4) log_pow_cancel nat_1_add_1 real_of_int_floor_add_one_ge real_sqrt_four real_sqrt_pow2)

  with \<open>threshold \<le> card (set xs)\<close> threshold_ge_2
  show \<open>?lower \<le> two_l_threshold\<close> by (simp add: nat_le_real_less)

  from
    \<open>threshold \<le> card (set xs)\<close> l_pos threshold_ge_2
    power_of_nat_log_le[of 2 \<open>4 * card (set xs) / \<lceil>threshold\<rceil>\<close>]
  show \<open>two_l_threshold \<le> ?upper\<close>
    by (simp add: l_def field_simps nat_le_real_less)
qed

end

interpretation estimate_distinct \<open>nat \<lceil>threshold\<rceil>\<close> \<open>nat l\<close> 2 xs \<epsilon>
  apply unfold_locales
  using \<epsilon>(1)
  apply simp_all
  by (metis Distinct_Elems_Correctness_Usage.\<epsilon>_threshold_ge_12(2) Distinct_Elems_Correctness_Usage.threshold_ge_2 \<delta>(1) \<delta>(2) \<epsilon>(2) ceiling_mono ceiling_numeral nat_le_0 nat_mono nat_numeral_as_int of_nat_nat rel_simps(28) two_l_threshold_bounds(1) two_l_threshold_bounds(2) verit_la_generic)

lemma exp_minus_log_le :
  assumes \<open>1 \<le> x\<close> \<open>0 < y\<close> \<open>y \<le> 1\<close>
  shows \<open>exp (- log 2 (8 * x / y)) \<le> y / (20 * x)\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  have
    \<open>?L = (y / (8 * x)) powr (1 / ln 2)\<close>
    (is \<open>_ = ?exponentiate (y / _)\<close>)
    using assms
    by (smt (verit, ccfv_threshold) divide_eq_0_iff ln_exp log_def log_divide log_ln nonzero_mult_div_cancel_left powr_def times_divide_eq_left)

  also have \<open>\<dots> \<le> ?R\<close>
  proof -
    have \<open>?exponentiate y \<le> y\<close>
      using assms(2,3) ln_2_less_1 powr_le_one_le by force

    moreover have \<open>?exponentiate x \<ge> x\<close>
      by (smt (verit, best) assms(1) less_divide_eq_1_pos ln_2_less_1 ln_gt_zero powr_mono powr_one)

    moreover have \<open>?exponentiate 8 \<ge> 20\<close> by (approximation 13)

    ultimately show ?thesis
      apply (simp add: powr_divide powr_mult)
      using
        assms(1) powr_ge_zero[of y "1 / ln 2"] frac_le[of y "y powr (1 / ln 2)" "20 * x" "8 powr (1 / ln 2) * x powr (1 / ln 2)"]
        mult_mono[of "20" "8 powr (1 / ln 2)" x "x powr (1 / ln 2)"]
      by argo
  qed

  finally show ?thesis .
qed

lemma
  \<open>prob_fail_bound \<le> \<delta> / 8\<close>
proof -
  show ?thesis
    apply (simp add: estimate_distinct_basic.prob_fail_bound_def threshold_def)
    sorry
qed

end


end