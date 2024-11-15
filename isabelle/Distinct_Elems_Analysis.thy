section \<open> TODO \<close>
theory Distinct_Elems_Analysis

imports
  Error_Bounds_K_Exceeds_L
  Error_Bounds_Est_Out_Of_Range

begin

context
  fixes
    threshold l r :: nat and
    \<epsilon> :: real and
    xs
  assumes params :
    \<open>2 \<le> r\<close> \<open>r \<le> threshold\<close> \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> 
    \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close>
    \<open>2 ^ l * threshold \<in> {r * card (set xs) .. 2 * r * card (set xs)}\<close>
begin

interpretation with_params :
  with_threshold_pos_r_l_xs threshold r l xs
  apply unfold_locales
  using \<open>2 \<le> r\<close> \<open>r \<le> threshold\<close> by simp

theorem estimate_distinct_error_bound :
  defines
    [simp] :
      \<open>prob_fail_bound \<equiv> real (length xs) / 2 ^ threshold\<close> and
    [simp] :
      \<open>prob_eager_algo_k_gt_l_le_bound \<equiv>
        real (length xs) *
        exp (-3 * real threshold * (r - 1)\<^sup>2 / (5 * r + 2 * r\<^sup>2))\<close> and
    [simp] :
      \<open>prob_eager_algo_k_le_l_and_estimate_out_of_range_bound \<equiv>
        4 * exp (-\<epsilon>\<^sup>2 * threshold / (4 * real r * (1 + 1 * \<epsilon> / 3)))\<close>
  shows
    \<open>\<P>(estimate in with_params.estimate_distinct xs.
        estimate |> fail_or_satisfies
          (\<lambda> estimate. real estimate >[\<epsilon>] card (set xs)))
    \<le> prob_fail_bound +
      prob_eager_algo_k_gt_l_le_bound +
      prob_eager_algo_k_le_l_and_estimate_out_of_range_bound\<close>
    (is \<open>?L \<le> _\<close>)
proof -
  let ?run_eager_algo =
    \<open>with_params.run_with_bernoulli_matrix <|
      run_reader <<< with_params.eager_algorithm\<close>

  have \<open>?L \<le>
    prob_fail_bound +
    \<P>(estimate in with_params.estimate_distinct_no_fail xs.
      real estimate >[\<epsilon>] card (set xs))\<close>
    using with_params.prob_estimate_distinct_fail_or_satisfies_le by simp

  also have \<open>\<dots> \<le> (
    prob_fail_bound +
    \<P>(state in ?run_eager_algo. state_k state > l) +
    \<P>(state in ?run_eager_algo. 
      state_k state \<le> l \<and> real (compute_estimate state) >[\<epsilon>] card (set xs)))\<close>
    by (auto
      intro: with_params.prob_estimate_distinct_fail_or_satisfies_le pmf_add
      simp add:
        with_params.estimate_distinct_no_fail_eq_lazy_algo
        with_params.eager_lazy_conversion[of _ \<open>length xs\<close>])

  finally show ?thesis
    using
      with_params.prob_eager_algo_k_gt_l_le assms
      with_params.prob_eager_algo_k_le_l_and_est_out_of_range_le
      params \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close>
    by force
qed

end

lemma
  fixes \<epsilon> \<delta> xs
  assumes \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> \<open>0 < \<delta>\<close> \<open>\<delta> \<le> 1\<close>
  defines
    [simp] : \<open>threshold \<equiv> 12 * log 2 (8 * real (length xs) / \<delta>) / \<epsilon>\<^sup>2\<close>
  shows
    \<open>\<P>(estimate in with_threshold.estimate_distinct (nat \<lceil>threshold\<rceil>) xs.
      estimate |> fail_or_satisfies
        (\<lambda> estimate. real estimate >[\<epsilon>] card (set xs)))
    \<le> \<delta>\<close>
proof (cases xs)
  case Nil
  then show ?thesis
    using assms
    by (simp add:
      with_threshold.estimate_distinct_def run_steps_then_estimate_def
      compute_estimate_def initial_state_def)
next
  let ?l = \<open>nat \<lfloor>log 2 <| 4 * card (set xs) / nat \<lceil>threshold\<rceil>\<rfloor>\<close>

  case (Cons _ _)
  then have \<open>length xs > 0\<close> by simp

  note assms = assms this

  note estimate_distinct_error_bound[of 2 \<open>nat \<lceil>threshold\<rceil>\<close> \<epsilon> ?l xs] assms

  moreover have
    \<open>nat \<lceil>threshold\<rceil> \<ge> 2\<close>
    proof - 
      have \<open>threshold \<ge> 2\<close>
        using assms
        apply (simp add: field_simps)
        by (smt (verit, del_insts) Num.of_nat_simps(1) \<open>0 < length xs\<close> log_divide_pos log_le_zero_cancel_iff nat_less_real_le one_le_log_cancel_iff power_le_one)

      then show ?thesis by linarith
    qed

  moreover have \<open>\<epsilon>\<^sup>2 * nat \<lceil>threshold\<rceil> \<ge> 12\<close>
  proof -
    from assms
    have \<open>\<epsilon>\<^sup>2 * threshold \<ge> 12\<close>
      using verit_comp_simplify1(3)[of "1" "length xs"]
      by (auto simp add: field_simps)

    then show ?thesis
      by (meson assms(1) dual_order.trans landau_o.R_mult_left_mono less_imp_le of_nat_ceiling zero_less_power)
  qed

  moreover have
    \<open>2 * card (set xs) \<le> 2 ^ ?l * nat \<lceil>threshold\<rceil>\<close>
  proof -
    define x where
      \<open>x \<equiv> card (set xs) / nat \<lceil>threshold\<rceil>\<close>

    show ?thesis when
      \<open>log 2 (2 * x) \<le> ?l\<close> (is ?thesis)
      using that assms \<open>nat \<lceil>threshold\<rceil> \<ge> 2\<close>
      apply (subst (asm) Transcendental.log_le_iff)
      apply (simp_all add: x_def)
      apply (metis List.finite_set card_gt_0_iff nat_0_iff of_nat_0_less_iff rel_simps(51) set_empty2 verit_comp_simplify(3) zero_compare_simps(6,7) zero_less_nat_eq)
      by (smt (verit, del_insts) Multiseries_Expansion.intyness_simps(2,3,4) Num.of_nat_simps(4) Suc_1 divide_le_eq mult_2 of_nat_le_iff powr_realpow semiring_1_class.of_nat_simps(2))

    have \<open>log 2 (2 * x) = 1 + log 2 x\<close> (is \<open>?L = _\<close>)
      apply (subst log_mult_pos)
      using assms
      apply (simp_all add: log_mult_pos x_def)
      by (smt (verit, ccfv_SIG) List.finite_set Multiseries_Expansion.intyness_0 calculation(9) card_gt_0_iff mult_eq_0_iff mult_sign_intros(5) nat_ceiling_le_eq of_nat_0_less_iff of_nat_le_0_iff
        of_nat_mono power2_less_0 set_empty2 threshold_def zero_compare_simps(7))
    
    also have \<open>\<dots> \<le> 2 + \<lfloor>log 2 x\<rfloor>\<close>
      apply simp
      by linarith

    also have \<open>\<dots> = \<lfloor>log 2 <| 4 * x\<rfloor>\<close> (is \<open>_ = ?R\<close>)
      apply (subst log_mult_pos)
      using assms
      apply (simp_all add: log_mult_pos x_def)
      apply (metis List.finite_set \<open>2 \<le> nat \<lceil>threshold\<rceil>\<close> assms(5) card_gt_0_iff divide_pos_pos of_nat_0_less_iff rel_simps(28) set_empty2 zero_order(4))
      by (metis (no_types, opaque_lifting) four_x_squared int_add_floor log2_of_power_eq more_arith_simps(6) of_int_add of_int_numeral of_nat_numeral of_nat_power power_one)
     
    finally show ?thesis by (simp add: x_def)
  qed

  moreover have
    \<open>2 ^ ?l * nat \<lceil>threshold\<rceil> \<le> 4 * card (set xs)\<close>
  proof -
    define x where
      \<open>x \<equiv> 4 * card (set xs) / nat \<lceil>threshold\<rceil>\<close>

    have \<open>\<lfloor>log 2 x\<rfloor> \<le> log 2 x\<close> using of_int_floor_le by blast

    have \<open>2 ^ ?l \<le> 4 * card (set xs) / nat \<lceil>threshold\<rceil>\<close>
      sorry

    show ?thesis sorry
  qed

  ultimately show ?thesis
    sorry
qed

end