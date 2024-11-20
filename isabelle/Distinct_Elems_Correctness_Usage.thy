theory Distinct_Elems_Correctness_Usage

imports
  "HOL-Decision_Procs.Approximation"
  CVM.Distinct_Elems_Correctness

begin

lemma exp_minus_log_le :
  assumes \<open>1 \<le> a\<close> \<open>1 \<le> b\<close> \<open>0 < c\<close> \<open>c \<le> 1\<close> 
  shows \<open>exp (- a * log 2 (8 * b / c)) \<le> c / (20 * b)\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  from assms have
    \<open>?L \<le> (c / (8 * b)) powr (1 / ln 2)\<close> (is \<open>_ \<le> ?exponentiate (c / _)\<close>)
    by (smt (verit, ccfv_threshold) divide_pos_pos exp_gt_zero le_divide_eq_1_pos ln_exp ln_ge_iff log_divide_pos log_eq_div_ln_mult_log log_le_zero_cancel_iff log_ln
      more_arith_simps(7) nonzero_mult_div_cancel_right powr_def)

  also have \<open>\<dots> \<le> ?R\<close>
  proof -
    have \<open>?exponentiate 8 \<ge> 20\<close> by (approximation 13)

    then have \<open>?exponentiate (8 * b) \<ge> 20 * b\<close>
      apply (simp only: powr_mult)
      by (metis Groups.mult_ac(2) assms(2) exp_ge_add_one_self exp_gt_zero log_exp mult_2 mult_mono one_le_log_cancel_iff one_less_numeral_iff powr_ge_zero powr_mono powr_one
        rel_simps(9) verit_prod_simplify(2) zero_less_one_class.zero_le_one)

    with assms show ?thesis
      apply (simp only: power_mult powr_divide)
      by (smt (verit, best) frac_le le_divide_eq_1 ln_2_less_1 ln_gt_zero_iff powr_le_one_le)
  qed

  finally show ?thesis .
qed

context
  fixes
    \<epsilon> \<delta> :: real and
    xs :: \<open>'a list\<close>
  assumes
    \<epsilon> : \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> and
    \<delta> : \<open>0 < \<delta>\<close> \<open>\<delta> \<le> 1\<close>
begin

abbreviation \<open>length_xs_1 \<equiv> max 1 (length xs)\<close>

definition \<open>threshold \<equiv> (12 / \<epsilon>\<^sup>2) * log 2 (8 * length_xs_1 / \<delta>)\<close>

definition \<open>l \<equiv> \<lfloor>log 2 <| 4 * card (set xs) / \<lceil>threshold\<rceil>\<rfloor>\<close>

context
  assumes
    \<open>xs \<noteq> []\<close>
    \<open>threshold \<le> card (set xs)\<close>
begin

lemma threshold_ge_2 :
  \<open>\<lceil>threshold\<rceil> \<ge> 2\<close>
  using \<epsilon> \<delta> \<open>xs \<noteq> []\<close>
  apply (simp add: threshold_def log_divide log_mult nonempty_iff_length_ge_1 field_simps)
  by (smt (verit, best) log_le_one_cancel_iff log_le_zero_cancel_iff log_less_zero_cancel_iff numeral_nat(7) one_of_nat_le_iff power_le_one) 

lemma \<epsilon>_threshold_ge_12 :
  \<open>\<epsilon>\<^sup>2 * \<lceil>threshold\<rceil> \<ge> 12\<close>
  using \<epsilon> \<delta> \<open>xs \<noteq> []\<close>
  apply (simp add: threshold_def nonempty_iff_length_ge_1 field_simps)
  by (smt (verit) Num.of_nat_simps(2) ceiling_divide_upper log_divide_pos log_le_zero_cancel_iff mult.commute numeral_nat(7) of_nat_mono one_le_log_cancel_iff
    zero_less_power)

lemma two_l_threshold_bounds :
  defines [simp] : \<open>two_l_threshold \<equiv> 2 ^ nat l * nat \<lceil>threshold\<rceil>\<close>
  shows
    \<open>2 * card (set xs) \<le> two_l_threshold\<close> (is \<open>?lower \<le> _\<close>)
    \<open>two_l_threshold \<le> 4 * card (set xs)\<close> (is \<open>_ \<le> ?upper\<close>)
proof -
  have \<open>l > 0\<close>
    using \<open>threshold \<le> card (set xs)\<close> threshold_ge_2
    apply (simp add: l_def field_simps)
    by linarith

  with \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close> threshold_ge_2
  have \<open>log 2 ?lower \<le> log 2 two_l_threshold\<close>
    apply (simp add: l_def log_mult log_divide field_simps split: if_splits)
    by (smt (z3) Num.of_nat_simps(2) log2_of_power_eq numeral_Bit0_eq_double numeral_code(1) of_nat_eq_numeral_iff power2_eq_square real_of_int_floor_add_one_ge)

  with \<open>threshold \<le> card (set xs)\<close> threshold_ge_2
  show \<open>?lower \<le> two_l_threshold\<close> by (simp add: nat_le_real_less)

  from
    \<open>threshold \<le> card (set xs)\<close> \<open>l > 0\<close> threshold_ge_2
    power_of_nat_log_le[of 2 \<open>4 * card (set xs) / \<lceil>threshold\<rceil>\<close>]
  show \<open>two_l_threshold \<le> ?upper\<close>
    by (simp add: l_def field_simps nat_le_real_less)
qed

end

interpretation estimate_distinct \<open>nat \<lceil>threshold\<rceil>\<close> 2 \<open>nat l\<close> \<epsilon> xs
  apply unfold_locales
  using \<epsilon>(1)
  apply simp_all
  by (smt (verit, best) Suc_1 \<epsilon>(2) \<epsilon>_threshold_ge_12 nat_2 nat_mono numeral_nat(7) of_nat_nat threshold_ge_2 two_l_threshold_bounds(1,2))

lemma prob_fail_bound_le_\<delta> :
  \<open>prob_fail_bound \<le> \<delta> / 8\<close>
proof -
  have \<open>prob_fail_bound \<le> length xs / (8 * length_xs_1 / \<delta>)\<close>
    apply (simp only: estimate_distinct_basic.prob_bounds_defs threshold_def Multiseries_Expansion.intyness_simps)
    by (smt (verit, best) \<delta>(1) \<epsilon>(1,2) divide_le_eq_1_pos divide_mono divide_pos_pos less_log_of_power max_nat.eq_neutr_iff mult_eq_0_iff nonzero_mult_div_cancel_right of_nat_0_le_iff
      of_nat_le_0_iff of_nat_le_1_iff of_nat_power power_le_one real_nat_ceiling_ge rel_simps(2,26,93) zero_less_power) 

  with \<delta> show ?thesis by (cases \<open>length xs = 0\<close>; simp)
qed

lemma prob_k_gt_l_bound_le_\<delta> :
  \<open>prob_k_gt_l_bound \<le> \<delta> / 20\<close>
proof -
  have
    \<open>prob_k_gt_l_bound \<le> real (length xs) * exp (- threshold / 6)\<close>
    by (simp add: estimate_distinct_basic.prob_bounds_defs landau_o.R_mult_left_mono real_nat_ceiling_ge)

  also have \<open>\<dots> \<le> length xs * \<delta> / (20 * length_xs_1)\<close>
    using exp_minus_log_le[of \<open>2 / \<epsilon>\<^sup>2\<close> \<open>length_xs_1\<close> \<delta>] \<epsilon> \<delta>
    apply (simp add: threshold_def)
    by (smt (verit) landau_o.R_mult_left_mono of_nat_0_le_iff power_le_one times_divide_eq_right)

  finally show ?thesis using \<delta> by (cases \<open>length xs = 0\<close>; simp)
qed

lemma prob_k_le_l_and_est_out_of_range_bound_le_\<delta> :
  \<open>prob_k_le_l_and_est_out_of_range_bound \<le> \<delta> / 5\<close>
proof -
  from \<epsilon> have
    \<open>prob_k_le_l_and_est_out_of_range_bound
    \<le> 4 * exp (-\<epsilon>\<^sup>2 * threshold / (8 * (1 + \<epsilon> / 3)))\<close>
    by (simp add: estimate_distinct_basic.prob_bounds_defs frac_le of_nat_ceiling)

  also have \<open>\<dots> \<le> \<delta> / (5 * length_xs_1)\<close>
    using exp_minus_log_le[of \<open>12 / (8 * (1 + \<epsilon> / 3))\<close> \<open>length_xs_1\<close> \<delta>] \<epsilon> \<delta>
    by (simp add: threshold_def)

  finally show ?thesis
    apply (simp add: field_simps)
    by (smt (verit, best) Num.of_nat_simps(2) approximation_preproc_nat(8) exp_gt_zero mult_le_cancel_right1 numeral_nat(7) prob_bounds_defs(3))
qed

theorem
  \<open>\<P>(estimate in estimate_distinct xs.
    estimate |> fails_or_satisfies
      (\<lambda> estimate. real estimate >[\<epsilon>] card (set xs)))
  \<le> 3 * \<delta> / 8\<close>
  using
    estimate_distinct_error_bound prob_fail_bound_le_\<delta>
    prob_k_gt_l_bound_le_\<delta> prob_k_le_l_and_est_out_of_range_bound_le_\<delta>
  by simp

end

end