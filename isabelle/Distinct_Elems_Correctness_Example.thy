theory Distinct_Elems_Correctness_Example

imports
  "HOL-Decision_Procs.Approximation"
  CVM.Distinct_Elems_Correctness
  CVM.Utils_Compat_Real

begin

lemma exp_minus_log_le :
  assumes \<open>1 \<le> a\<close> \<open>1 \<le> b\<close> \<open>0 < c\<close> \<open>c \<le> 1\<close> 
  shows \<open>exp (- a * log 2 (8 * b / c)) \<le> c / (20 * b)\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  from assms have
    \<open>?L \<le> (c / (8 * b)) powr (1 / ln 2)\<close> (is \<open>_ \<le> ?exponentiate (c / _)\<close>)
    by (smt (verit, ccfv_threshold) divide_pos_pos exp_gt_zero le_divide_eq_1_pos ln_exp ln_ge_iff log_divide_pos' log_eq_div_ln_mult_log log_le_zero_cancel_iff log_ln
      more_arith_simps(7) nonzero_mult_div_cancel_right powr_def)

  also have \<open>\<dots> \<le> ?R\<close>
  proof -
    have \<open>?exponentiate 8 \<ge> 20\<close> by (approximation 13)

    then have \<open>?exponentiate (8 * b) \<ge> 20 * b\<close>
      using
        \<open>1 \<le> b\<close> ln_2_less_1 powr_mono[of "1" "1 / ln 2" b]
        mult_mono[of "20" "8 powr (1 / ln 2)" b "b powr (1 / ln 2)"]
      by (auto simp add: powr_mult)

    with assms show ?thesis
      apply (simp only: powr_divide)
      by (smt (verit, best) frac_le le_divide_eq_1 ln_2_less_1 ln_gt_zero_iff powr_le_one_le)
  qed

  finally show ?thesis .
qed

context
  fixes
    \<epsilon> \<delta> :: real and
    xs :: \<open>'a list\<close>
begin

abbreviation (input) \<open>length_xs_1 \<equiv> max 1 (length xs)\<close>

definition \<open>threshold \<equiv> (12 / \<epsilon>\<^sup>2) * log 2 (8 * length_xs_1 / \<delta>)\<close>

definition \<open>l \<equiv> \<lfloor>log 2 <| 4 * card (set xs) / \<lceil>threshold\<rceil>\<rfloor>\<close>

context
  assumes
    \<epsilon> : \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> and
    \<delta> : \<open>0 < \<delta>\<close> \<open>\<delta> \<le> 1\<close>
begin

context
  assumes
    \<open>xs \<noteq> []\<close>
    \<open>threshold \<le> card (set xs)\<close>
begin

lemma threshold_ge_2 :
  \<open>\<lceil>threshold\<rceil> \<ge> 2\<close>
  using \<epsilon> \<delta> \<open>xs \<noteq> []\<close>
  apply (simp add: threshold_def log_divide log_mult nonempty_iff_length_ge_1 field_simps)
  by (smt (verit, best) log_le_one_cancel_iff log_le_zero_cancel_iff log_less_zero_cancel_iff numeral_nat(7) one_power2 power_mono real_of_nat_ge_one_iff)

lemma \<epsilon>_threshold_ge_12 :
  \<open>\<epsilon>\<^sup>2 * \<lceil>threshold\<rceil> \<ge> 12\<close>
  using \<epsilon> \<delta> \<open>xs \<noteq> []\<close>
  apply (simp add: threshold_def nonempty_iff_length_ge_1 field_simps)
  by (smt (verit) Num.of_nat_simps(2) ceiling_divide_upper log_divide_pos' log_le_zero_cancel_iff mult.commute numeral_nat(7) of_nat_mono one_le_log_cancel_iff
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
    by (smt (verit, ccfv_SIG) Num.of_nat_simps(2) Num.of_nat_simps(4) log2_of_power_eq of_nat_numeral one_add_one real_of_int_floor_add_one_ge real_of_nat_eq_numeral_power_cancel_iff real_sqrt_four real_sqrt_pow2)

  with \<open>threshold \<le> card (set xs)\<close> threshold_ge_2
  show \<open>?lower \<le> two_l_threshold\<close> by (simp add: nat_le_real_less)

  from
    \<open>threshold \<le> card (set xs)\<close> \<open>l > 0\<close> threshold_ge_2
    power_of_nat_log_le[of 2 \<open>?upper / \<lceil>threshold\<rceil>\<close>]
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
  from \<epsilon> \<delta> have \<open>prob_fail_bound \<le> length xs / (8 * length_xs_1 / \<delta>)\<close>
    apply (simp only: estimate_distinct_basic.prob_bounds_defs threshold_def)
    by (smt (verit, ccfv_SIG) Multiseries_Expansion.intyness_0 divide_le_eq_1_pos frac_le divide_pos_pos less_log_of_power max_nat.eq_neutr_iff mult_eq_0_iff mult_le_cancel_right1
      of_nat_le_0_iff power_le_one real_nat_ceiling_ge rel_simps(76,93) zero_less_power)
 
  with \<delta> show ?thesis by (cases \<open>length xs = 0\<close>; simp)
qed

lemma prob_k_gt_l_bound_le_\<delta> :
  \<open>prob_k_gt_l_bound \<le> \<delta> / 20\<close>
proof -
  have \<open>prob_k_gt_l_bound \<le> length xs * exp (- threshold / 6)\<close>
    by (simp add: estimate_distinct_basic.prob_bounds_defs landau_o.R_mult_left_mono real_nat_ceiling_ge)

  also have \<open>\<dots> \<le> length xs * \<delta> / (20 * length_xs_1)\<close>
    using exp_minus_log_le[of \<open>2 / \<epsilon>\<^sup>2\<close> \<open>length_xs_1\<close> \<delta>] \<epsilon> \<delta>
    apply (simp add: threshold_def)
    by (smt (verit, ccfv_SIG) landau_o.R_mult_left_mono max_def numeral_nat(7) of_nat_0_le_iff power_le_one_iff real_of_nat_ge_one_iff rel_simps(47) times_divide_eq_right)

  finally show ?thesis using \<delta> by (cases \<open>length xs = 0\<close>; simp)
qed

lemma prob_k_le_l_and_est_out_of_range_bound_le_\<delta> :
  \<open>prob_k_le_l_and_est_out_of_range_bound \<le> \<delta> / 5\<close>
  using exp_minus_log_le[of \<open>12 / (8 * (1 + \<epsilon> / 3))\<close> \<open>length_xs_1\<close> \<delta>] \<epsilon> \<delta>
  apply (simp
    add:
      estimate_distinct_basic.prob_bounds_defs threshold_def field_split_simps
      real_of_nat_ge_one_iff
    split: if_splits)
  by (smt (verit, ccfv_SIG) Groups.mult_ac(2) Num.of_nat_simps(1) ceiling_divide_upper divide_le_eq_1_pos frac_le exp_le_cancel_iff log_le_zero_cancel_iff
    mult_le_cancel_right1 nat_less_real_le zero_less_power)

theorem estimate_distinct_example_correct :
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

thm estimate_distinct_example_correct threshold_def

end