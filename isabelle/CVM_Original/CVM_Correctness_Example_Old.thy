theory CVM_Correctness_Example_Old

imports
  CVM_Correctness

begin

lemma exp_minus_log_le :
  assumes \<open>1 \<le> a\<close> \<open>1 \<le> b\<close> \<open>0 < c\<close> \<open>c \<le> 1\<close> 
  shows \<open>exp (- a * log 2 (3 * b / c)) \<le> c / (4 * b)\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  from assms
  have \<open>?L = exp (log 2 <| (c / (3 * b)) powr a)\<close>
    by (simp add: field_simps log_powr log_divide_pos)

  also from assms
  have \<open>\<dots> = ((c / (3 * b)) powr a) powr (1 / ln 2)\<close>
    by (simp add: powr_def)

  also from assms
  have \<open>\<dots> \<le> (c / (3 * b)) powr (1 / ln 2)\<close> (is \<open>_ \<le> ?exponentiate (c / _)\<close>)
    by (simp add: powr_le_one_le powr_mono2)

  also have \<open>\<dots> \<le> ?R\<close>
  proof -
    have \<open>?exponentiate 3 \<ge> 4\<close> by (approximation 5)

    with assms ln_2_less_1 have \<open>?exponentiate (3 * b) \<ge> 4 * b\<close>
      apply (simp add: field_simps powr_mult)
      sorry
      (* using mult_mono[of "20" "3 powr (Numeral1 / ln 2)" b "b powr (Numeral1 / ln 2)"] powr_mono[of Numeral1 "Numeral1 / ln 2" b]
      by (fastforce simp add: powr_mult) *)

    with assms ln_2_less_1 show ?thesis
      by (simp add: powr_divide frac_le powr_le_one_le)
  qed

  finally show ?thesis .
qed

context
  fixes
    \<epsilon> \<delta> :: real and
    xs :: \<open>'a list\<close>
begin

abbreviation (input) \<open>length_xs_1 \<equiv> max (Suc 0) (length xs)\<close>

definition \<open>threshold \<equiv> 12 / \<epsilon>\<^sup>2 * log 2 (3 * length_xs_1 / \<delta>)\<close>

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
  moreover from calculation
  have \<open>length_xs_1 = length xs\<close> by (simp add: Suc_le_eq)

  moreover note \<epsilon> \<delta>

  ultimately show ?thesis
    unfolding cvm_error_bounds.prob_bounds_defs threshold_def
    apply (simp add: field_simps)
    sorry
    (* by (smt (verit, best) Groups.mult_ac(2) Multiseries_Expansion.intyness_1 approximation_preproc_nat(8) divide_le_eq divide_le_eq_1_pos divide_mono log_base_pow log_le_one_cancel_iff
      log_le_zero_cancel_iff log_pow_cancel nat_le_real_less of_nat_le_iff power_le_one power_one_right real_nat_ceiling_ge zero_compare_simps(6) zero_less_power) *)
qed

lemma prob_k_gt_l_bound_le_\<delta> :
  \<open>prob_k_gt_l_bound \<le> \<delta> / 4\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  have \<open>?L \<le> length xs * exp (- threshold / 6)\<close>
    unfolding cvm_error_bounds.prob_bounds_defs
    by (simp add: field_simps mult_left_mono real_nat_ceiling_ge)

  also from exp_minus_log_le[of \<open>2 / \<epsilon>\<^sup>2\<close> \<open>length_xs_1\<close> \<delta>] \<epsilon> \<delta>
  have \<open>\<dots> \<le> length xs * \<delta> / (4 * length_xs_1)\<close>
    unfolding threshold_def
    apply (simp add: field_simps)
    by (smt (verit, del_insts) Groups.mult_ac(2) landau_o.R_mult_left_mono of_nat_0_le_iff power_le_one)
  
  also from \<delta> have \<open>\<dots> \<le> ?R\<close> by (cases \<open>xs = []\<close>) (simp_all add: field_simps)

  finally show ?thesis .
qed

lemma prob_k_le_l_and_est_out_of_range_bound_le_\<delta> :
  \<open>prob_k_le_l_and_est_out_of_range_bound \<le> \<delta>\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  from \<epsilon> have \<open>?L \<le> 4 * exp (-\<epsilon>\<^sup>2 * threshold / (8 * (1 + \<epsilon> / 3)))\<close>
    unfolding cvm_error_bounds.prob_bounds_defs
    apply (simp add: field_simps power_numeral_reduce)
    by (smt (verit, ccfv_SIG) eq_imp_le mult_le_cancel_left_pos nat_ceiling_le_eq)

  also from exp_minus_log_le[of \<open>12 / (8 * (1 + \<epsilon> / 3))\<close> \<open>length_xs_1\<close> \<delta>] \<epsilon> \<delta>
  have \<open>\<dots> \<le> \<delta> / length_xs_1\<close>
    unfolding threshold_def
    by simp

  also from \<delta> have \<open>\<dots> \<le> ?R\<close> by (simp add: field_simps)

  finally show ?thesis .
qed

theorem prob_cvm_incorrect_le_\<delta> :
  \<open>\<P>(estimate in cvm xs.
    estimate |> is_None_or_pred (\<lambda> estimate. estimate >[\<epsilon>] card (set xs)))
  \<le> \<delta>\<close>
  using
    prob_cvm_incorrect_le prob_fail_bound_le_\<delta>
    prob_k_gt_l_bound_le_\<delta> prob_k_le_l_and_est_out_of_range_bound_le_\<delta>
  by simp

end

end

(* corollary prob_cvm_incorrect_le_\<delta>' :
  assumes \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> \<open>0 < \<delta>\<close> \<open>\<delta> \<le> 1\<close>
  defines \<open>\<delta>' \<equiv> 3 * \<delta> / 8\<close>
  shows
    \<open>\<P>(estimate in cvm_algo.cvm (nat \<lceil>threshold \<epsilon> \<delta>' xs\<rceil>) xs.
      estimate |> is_None_or_pred (\<lambda> estimate. estimate >[\<epsilon>] card (set xs)))
    \<le> \<delta>\<close>
  using assms prob_cvm_incorrect_le_\<delta>[of \<epsilon> \<delta>' xs] by simp *)

end