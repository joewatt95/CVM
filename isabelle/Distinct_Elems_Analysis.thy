section \<open> TODO \<close>
theory Distinct_Elems_Analysis

imports
  CVM.Utils_PMF_Bernoulli_Binomial
  CVM.Utils_PMF_Hoare
  CVM.Error_Bounds_K_Exceeds_L
  CVM.Error_Bounds_Est_Out_Of_Range

begin

context with_threshold
begin

lemma estimate_distinct_correct_of_threshold :
  assumes \<open>threshold > card (set xs)\<close>
  shows \<open>estimate_distinct xs = return_spmf (card <| set xs)\<close>
proof -
  let ?step = \<open>\<lambda> x. case_option fail_spmf (step x)\<close>
  let ?P = \<open>\<lambda> index.
    (=) (Some \<lparr>state_k = 0, state_chi = set (take index xs)\<rparr>)\<close>

  have \<open>\<turnstile>pmf
    \<lbrakk>(\<lambda> state. (index, x) \<in> set (List.enumerate 0 xs) \<and> ?P index state)\<rbrakk>
    ?step x
    \<lbrakk>?P (Suc index)\<rbrakk>\<close> for index x
    using
      assms card_set_take_le_card_set[of "Suc index" xs]
      insert_nth_set_take_eq_set_take_Suc[of index xs]
    by (auto simp add:
      Utils_PMF_Hoare.hoare_triple_def step_def in_set_enumerate_eq)

  then have \<open>\<turnstile>pmf
    \<lbrakk>?P 0\<rbrakk>
    map_spmf compute_estimate <<< foldM_pmf ?step xs
    \<lbrakk>flip (=) (Some <| card <| set xs)\<rbrakk>\<close>
    using Utils_PMF_Hoare.loop[where offset = 0]
    by (force
      intro: Utils_PMF_Hoare.seq
      simp add: map_pmf_def compute_estimate_def)

  then show ?thesis
    using map_pmf_eq_return_pmf_iff
    by (force simp add:
      estimate_distinct_def run_steps_then_estimate_def initial_state_def
      foldM_spmf_eq_foldM_pmf_case Utils_PMF_Hoare.hoare_triple_def image_def)
qed

end

context
  fixes
    threshold l r :: nat and
    \<epsilon> :: real and
    xs :: \<open>'a list\<close>
begin

theorem estimate_distinct_error_bound :
  defines
    [simp] : \<open>F0 \<equiv> card (set xs)\<close> and
    [simp] :
      \<open>prob_fail_bound \<equiv> real (length xs) / 2 ^ threshold\<close> and
    [simp] :
      \<open>prob_eager_algo_k_gt_l_le_bound \<equiv>
        real (length xs) *
        exp (-3 * real threshold * (r - 1)\<^sup>2 / (5 * r + 2 * r\<^sup>2))\<close> and
    [simp] :
      \<open>prob_eager_algo_k_le_l_and_estimate_out_of_range_bound \<equiv>
        4 * exp (-\<epsilon>\<^sup>2 * threshold / (4 * real r * (1 + 1 * \<epsilon> / 3)))\<close>
  assumes
    \<open>0 < \<epsilon>\<close>
    \<open>threshold \<le> F0 \<Longrightarrow> (
      \<epsilon> \<le> 1 \<and>
      r \<in> {2 .. threshold} \<and>
      \<epsilon>\<^sup>2 * threshold \<ge> 6 * r \<and>
      2 ^ l * threshold \<in> {r * F0 .. 2 * r * F0})\<close>
  shows
    \<open>\<P>(estimate in with_threshold.estimate_distinct threshold xs.
        estimate |> fail_or_satisfies
          (\<lambda> estimate. real estimate >[\<epsilon>] card (set xs)))
    \<le> prob_fail_bound +
      prob_eager_algo_k_gt_l_le_bound +
      prob_eager_algo_k_le_l_and_estimate_out_of_range_bound\<close>
    (is \<open>?L \<le> _\<close>)
proof (cases \<open>threshold > F0\<close>)
  case True
  then have \<open>?L = 0\<close>
    using \<open>\<epsilon> > 0\<close> zero_compare_simps(10)[of "\<bar>\<epsilon>\<bar>" "real (card (set xs))"]
    by (simp add: with_threshold.estimate_distinct_correct_of_threshold)

  then show ?thesis by simp
next
  case False
  then have \<open>threshold \<le> F0\<close> by simp

  with assms interpret with_params :
    with_threshold_pos_r_l_xs threshold r l xs
    apply unfold_locales by simp

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
      intro: pmf_add
      simp add:
        with_params.estimate_distinct_no_fail_eq_lazy_algo
        with_params.eager_lazy_conversion[of _ \<open>length xs\<close>])

  finally show ?thesis
    using
      with_params.prob_eager_algo_k_gt_l_le assms
      with_params.prob_eager_algo_k_le_l_and_est_out_of_range_le
      assms \<open>threshold \<le> F0\<close>
    by force
qed

end

lemma
  fixes \<epsilon> \<delta> xs
  assumes \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> \<open>0 < \<delta>\<close> \<open>\<delta> \<le> 1\<close>
  defines
    \<open>threshold \<equiv> nat \<lceil>12 * log 2 (8 * real (length xs) / \<delta>) / \<epsilon>\<^sup>2\<rceil>\<close>
  shows
    \<open>\<P>(estimate in with_threshold.estimate_distinct threshold xs.
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
  case (Cons _ _)

  define x where
    \<open>x \<equiv> card (set xs) / threshold\<close>

  let ?l = \<open>nat \<lfloor>log 2 <| 4 * x\<rfloor>\<close>

  (* note estimate_distinct_error_bound[of 2 threshold \<epsilon> ?l xs] *)

  have \<open>threshold \<ge> 2\<close>
    using assms
    apply (simp add: Cons log_divide)
    by (smt (verit, best) Multiseries_Expansion.intyness_simps(4) Num.of_nat_simps(4) divide_le_eq_1_pos log_le_one_cancel_iff log_le_zero_cancel_iff nat_le_real_less of_nat_0_le_iff one_add_one one_power2 power_mono real_nat_ceiling_ge zero_less_power)

  moreover have \<open>x > 0\<close>
    using \<open>threshold \<ge> 2\<close>
    apply (simp add: x_def Cons)
    by (metis List.finite_set bot_nat_0.not_eq_extremum card_0_eq list.distinct(2) list.simps(15) not_numeral_le_zero of_nat_0_less_iff set_empty2 zero_less_divide_iff)

  moreover have \<open>\<epsilon>\<^sup>2 * threshold \<ge> 12\<close>
    using assms \<open>x > 0\<close> \<open>threshold \<ge> 2\<close>
    apply simp
    by (smt (z3) Groups.mult_ac(2) ceiling_le_zero divide_le_eq log_divide log_le_one_cancel_iff log_le_zero_cancel_iff nat_le_0 of_nat_le_0_iff of_nat_less_1_iff
      real_nat_ceiling_ge rel_simps(28) zero_compare_simps(7))
  
  moreover have
    \<open>2 * card (set xs) \<le> 2 ^ ?l * threshold\<close>
  proof -
    have \<open>log 2 (2 * x) \<le> ?l\<close>
      using \<open>x > 0\<close>
      apply (simp add: log_mult)
      apply (simp only: Multiseries_Expansion.intyness_simps)
      by (smt (verit, ccfv_SIG) Multiseries_Expansion.intyness_1 One_nat_def Suc_1 log2_of_power_eq nat_2 numeral_Bit0_eq_double of_int_1 of_int_add of_nat_0_le_iff of_nat_nat
        power2_eq_square real_of_int_floor_add_one_ge zero_le_floor)

    then show ?thesis
      using \<open>x > 0\<close> \<open>threshold \<ge> 2\<close> 
      apply (simp add: log_mult x_def)
      apply (simp only: Multiseries_Expansion.intyness_simps)
      by (smt (verit, ccfv_threshold) Num.of_nat_simps(5) divide_le_eq le_num_simps(2) less_log_of_power nat_le_real_less of_nat_le_1_iff of_nat_power
        verit_comp_simplify(6))
  qed

  moreover have
    \<open>2 ^ ?l * nat \<lceil>threshold\<rceil> \<le> 4 * card (set xs)\<close>
  proof -
    (* See comments on the context assms for how to discharge this. *)
    have \<open>x \<ge> 1\<close> sorry

    then have \<open>2 ^ ?l \<le> 4 * x\<close> by (simp add: power_of_nat_log_le)

    with \<open>threshold \<ge> 2\<close>
    show ?thesis
      apply (simp add: x_def)
      apply (simp only: Multiseries_Expansion.intyness_simps)
      by (smt (verit, ccfv_threshold) Num.of_nat_simps(5) divide_le_eq nonzero_eq_divide_eq of_nat_eq_0_iff of_nat_le_iff semiring_norm(95))
  qed

  ultimately show ?thesis
    sorry
qed

end