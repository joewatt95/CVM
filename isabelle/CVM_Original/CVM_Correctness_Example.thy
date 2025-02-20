theory CVM_Correctness_Example

imports
  CVM_Correctness

begin

lemma exp_minus_log_le :
  assumes \<open>9/8 \<le> a\<close> \<open>2 \<le> b\<close> \<open>0 < c\<close> \<open>c \<le> 1\<close>
  shows \<open>exp (- a * log 2 (3 * b / c)) \<le> 2*c / (15 * b)\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  have \<open>?L \<le> exp (- (9/8) * log 2 (3 * b / c))\<close> using assms
    by (intro iffD2[OF exp_le_cancel_iff] mult_right_mono iffD2[OF zero_le_log_cancel_iff]) auto
  also have \<open>\<dots> \<le> exp ( log 2 (1 / (3 * b / c)) * (9/8))\<close>
    unfolding log_recip by simp
  also have \<open>\<dots> = exp (ln (c / (3 * b)) * (9/(8*ln 2)))\<close>
    unfolding log_def by (simp add:divide_simps)
  also have \<open>\<dots> = ((1-2*c/b) *\<^sub>R 0 + (2*c /b) *\<^sub>R (1/6)) powr (9/(8*ln 2))\<close>
    using assms unfolding powr_def by (auto simp:algebra_simps)
  also have \<open>\<dots> \<le> (1-2*c/b) * 0 powr (9/(8*ln 2)) + (2*c /b) * (1/6) powr (9/(8*ln 2))\<close>
    apply (intro convex_onD[OF convex_powr])
    subgoal by (approximation 10)
    by (use assms in auto)
  also have \<open>\<dots> = (c/b) * (2*(1/6) powr (9/(8*ln 2)))\<close> by simp
  also have \<open>\<dots> \<le> (c/b) * (2/15)\<close>
    apply (intro mult_left_mono)
    subgoal by (approximation 10)
    by (use assms in auto)
  also have \<open>\<dots> = ?R\<close> by simp
  finally show ?thesis by simp
qed

context
  fixes
    \<epsilon> \<delta> :: real and
    xs :: \<open>'a list\<close>
begin

abbreviation (input) \<open>length_xs_1 \<equiv> max (Suc 0) (length xs)\<close>

definition \<open>threshold \<equiv> (12 / \<epsilon>\<^sup>2) * log 2 (3 * length_xs_1 / \<delta>)\<close>

definition \<open>l \<equiv> \<lfloor>log 2 <| 4 * card (set xs) / \<lceil>threshold\<rceil>\<rfloor>\<close>

context
  assumes
    \<epsilon> : \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> and
    \<delta> : \<open>0 < \<delta>\<close> \<open>\<delta> \<le> 1\<close>
begin

context
  assumes \<open>xs \<noteq> []\<close>
begin

lemma threshold_ge_2 :
  \<open>\<lceil>threshold\<rceil> \<ge> 2\<close>
  using \<epsilon> \<delta> \<open>xs \<noteq> []\<close>
  apply (simp add: threshold_def)
  by (smt (verit, del_insts) Num.of_nat_simps(2) approximation_preproc_nat(8) log_divide_pos log_le_one_cancel_iff log_le_zero_cancel_iff numeral_nat(7) power2_nonneg_gt_1_iff)

lemma \<epsilon>_threshold_ge_12 :
  \<open>\<epsilon>\<^sup>2 * \<lceil>threshold\<rceil> \<ge> 12\<close>
  using \<epsilon> \<delta> \<open>xs \<noteq> []\<close>
  apply (simp add: threshold_def)
  by (smt (verit) Groups.mult_ac(2) approximation_preproc_nat(8) ceiling_divide_upper log_divide_pos log_le_zero_cancel_iff nat_le_real_less numeral_nat(7) one_le_log_cancel_iff one_of_nat_le_iff
    zero_less_power)

lemma two_l_threshold_bounds :
  assumes \<open>threshold \<le> card (set xs)\<close>
  defines [simp] : \<open>two_l_threshold \<equiv> 2 ^ nat l * nat \<lceil>threshold\<rceil>\<close>
  shows
    \<open>2 * card (set xs) \<le> two_l_threshold\<close> (is \<open>?lower \<le> _\<close>)
    \<open>two_l_threshold \<le> 4 * card (set xs)\<close> (is \<open>_ \<le> ?upper\<close>)
proof -
  from assms threshold_ge_2
  have \<open>l > 0\<close>
    apply (simp add: l_def field_simps)
    by linarith

  with assms threshold_ge_2
  have \<open>log 2 ?lower \<le> log 2 two_l_threshold\<close>
    apply (simp add: l_def log_mult_pos log_divide_pos)
    by (smt (verit, best) Num.of_nat_simps(2) floor_eq_iff log2_of_power_eq numeral_Bit0_eq_double numerals(1) of_nat_numeral power2_eq_square)

  with assms threshold_ge_2
  show \<open>?lower \<le> two_l_threshold\<close> by (simp add: nat_le_real_less)

  from
    assms \<open>l > 0\<close> threshold_ge_2
    power_of_nat_log_le[of 2 \<open>?upper / \<lceil>threshold\<rceil>\<close>]
  show \<open>two_l_threshold \<le> ?upper\<close>
    by (simp add: l_def field_simps nat_le_real_less)
qed

end

interpretation cvm_correctness \<open>nat \<lceil>threshold\<rceil>\<close> 2 \<open>nat l\<close> \<epsilon> xs
  apply unfold_locales
    subgoal by (intro \<epsilon>(1))
    subgoal
      using \<epsilon>(2) \<epsilon>_threshold_ge_12 threshold_ge_2 two_l_threshold_bounds
      apply simp
      using nat_mono threshold_ge_2 by presburger
    done

lemma prob_fail_bound_le_\<delta> :
  \<open>prob_fail_bound \<le> \<delta> / 3\<close>
proof (cases \<open>xs = []\<close>)
  case True
  with \<delta> show ?thesis unfolding cvm_error_bounds.prob_bounds_defs by simp
next
  case False
  with \<epsilon> \<delta> show ?thesis
    unfolding cvm_error_bounds.prob_bounds_defs threshold_def
    apply (simp add: field_simps)
    by (smt (verit, best) Groups.mult_ac(2) Multiseries_Expansion.intyness_1 approximation_preproc_nat(8) divide_le_eq divide_le_eq_1_pos divide_mono log_base_pow log_le_one_cancel_iff
      log_le_zero_cancel_iff log_pow_cancel nat_le_real_less of_nat_le_iff power_le_one power_one_right real_nat_ceiling_ge zero_compare_simps(6) zero_less_power)
qed

lemma prob_k_gt_l_bound_le_\<delta> :
  assumes \<open>length xs \<ge> 2\<close>
  shows \<open>prob_k_gt_l_bound \<le> 2 * \<delta> / 15\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  have \<open>9/8 \<le> (2::real)/1\<close> by simp
  also have \<open>\<dots> \<le> 2 / \<epsilon>^2\<close> using \<epsilon> by (intro divide_left_mono) (auto intro:power_le_one)
  finally have 0:\<open>9/8 \<le> 2 / \<epsilon>\<^sup>2\<close> by simp

  have \<open>?L \<le> length xs * exp (- threshold / 6)\<close>
    unfolding cvm_error_bounds.prob_bounds_defs
    by (simp add: field_simps mult_left_mono real_nat_ceiling_ge)

  also have \<open>\<dots> = real (length xs) * exp (- (2 / \<epsilon>^2) * log 2 (3* real length_xs_1 / \<delta>))\<close>
    unfolding threshold_def by (simp add: field_simps)
  also have \<open>\<dots> \<le> length xs * (2 * \<delta> / (15 * real length_xs_1))\<close>
    using 0 \<epsilon> \<delta> assms by (intro mult_left_mono exp_minus_log_le) auto
  also have \<open>\<dots> = 2*length xs * \<delta> / (15 * length_xs_1)\<close> by simp
  also from \<delta> have \<open>\<dots> \<le> ?R\<close> by (cases \<open>xs = []\<close>) (simp_all add: field_simps)
  finally show ?thesis .
qed

lemma prob_k_le_l_and_est_out_of_range_bound_le_\<delta> :
  assumes \<open>length xs \<ge> 2\<close>
  shows \<open>prob_k_le_l_and_est_out_of_range_bound \<le> 8 * \<delta> / 15\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  from \<epsilon> have \<open>?L \<le> 4 * exp (-\<epsilon>\<^sup>2 * threshold / (8 * (1 + \<epsilon> / 3)))\<close>
    unfolding cvm_error_bounds.prob_bounds_defs
    apply (simp add: field_simps power_numeral_reduce)
    by (smt (verit, ccfv_SIG) eq_imp_le mult_le_cancel_left_pos nat_ceiling_le_eq)
  also have \<open>\<dots> = 4 * exp (- (12 / (8 * (1 + \<epsilon> / 3))) * log 2 (3* real length_xs_1 / \<delta>))\<close>
    unfolding threshold_def using \<epsilon> by (simp add: algebra_simps)
  also have \<open>\<dots> \<le> 4 * (2 * \<delta> / (15 * real length_xs_1))\<close>
    using assms \<delta> \<epsilon> by (intro mult_left_mono exp_minus_log_le) (auto simp:divide_simps)
  also from \<delta> have \<open>\<dots> \<le> ?R\<close> by (simp add: field_simps)

  finally show ?thesis .
qed

theorem prob_cvm_incorrect_le_\<delta> :
  \<open>\<P>(estimate in cvm xs.
    estimate |> is_None_or_pred (\<lambda> estimate. estimate >[\<epsilon>] card (set xs)))
  \<le> \<delta>\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  note unfold_cvm =
    step_def step_1_def step_2_def initial_state_def compute_estimate_def

  consider (i) \<open>length xs = 0\<close> | (ii) \<open>length xs = 1\<close> | (iii) \<open>length xs \<ge> 2\<close>
    by linarith
  thus ?thesis
  proof (cases)
    case i thus ?thesis using \<delta> by (simp add:unfold_cvm)
  next
    case ii
    then obtain x where xs_def: \<open>xs = [x]\<close>
      by (metis One_nat_def Suc_length_conv length_0_conv)

    have 0:\<open> nat \<lceil>threshold\<rceil> \<noteq> 1\<close>
      using threshold_ge_2 xs_def real_nat_ceiling_ge by fastforce
    have \<open>?L = \<P>(estimate in cvm [x]. estimate |> is_None_or_pred (\<lambda> estimate. estimate >[\<epsilon>] 1))\<close>
      by (simp_all add:xs_def option.case_eq_if)
    also have \<open>\<dots> = 0\<close> using 0 \<epsilon>
      by (simp add:unfold_cvm bind_return_pmf Let_def step_3_def split:split_indicator)
    also have \<open>\<dots> \<le> \<delta>\<close> using \<delta> by simp
    finally show ?thesis by simp
  next
    case iii
    then show ?thesis using
      prob_fail_bound_le_\<delta> prob_cvm_incorrect_le
      prob_k_gt_l_bound_le_\<delta> prob_k_le_l_and_est_out_of_range_bound_le_\<delta>
      by simp
  qed
qed

end

end

end