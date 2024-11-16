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
    (* TODO:
    Tweak this API to allow the extra assumptions that `xs` is nonempty, and
    that `threshold` is strictly less than `F_0`, ie:

    \<open>\<lbrakk>xs \<noteq> []; threshold < card (set xs)\<rbrakk> \<Longrightarrow>
    2 ^ l * threshold \<in> {r * card (set xs) .. 2 * r * card (set xs)}\<close>

    Then discharge of these assumptions when applying our intermediate lemmas
    by arguing that the algorithm is always correct
    (ie P(fail of estimate out of range = 0)) if either of these conditions
    holds.
    *)
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
  case (Cons _ _)

  define x where
    \<open>x \<equiv> card (set xs) / nat \<lceil>threshold\<rceil>\<close>

  let ?l = \<open>nat \<lfloor>log 2 <| 4 * x\<rfloor>\<close>

  note estimate_distinct_error_bound[of 2 \<open>nat \<lceil>threshold\<rceil>\<close> \<epsilon> ?l xs] assms

  moreover have
    \<open>nat \<lceil>threshold\<rceil> \<ge> 2\<close>
    proof - 
      have \<open>threshold \<ge> 2\<close>
        using assms
        apply (simp add: field_simps Cons)
        by (smt (verit) log_divide_pos log_le_zero_cancel_iff of_nat_0_le_iff one_le_log_cancel_iff one_of_nat_le_iff powr_le_one_le powr_realpow rel_simps(25))

      then show ?thesis by linarith
    qed

  moreover have \<open>\<epsilon>\<^sup>2 * nat \<lceil>threshold\<rceil> \<ge> 12\<close>
  proof -
    from assms
    have \<open>\<epsilon>\<^sup>2 * threshold \<ge> 12\<close>
      by (simp add: Cons field_simps)

    then show ?thesis
      by (meson assms(1) dual_order.trans landau_o.R_mult_left_mono less_imp_le of_nat_ceiling zero_less_power)
  qed

  moreover have
    \<open>2 * card (set xs) \<le> 2 ^ ?l * nat \<lceil>threshold\<rceil>\<close>
  proof -
    show ?thesis when
      \<open>log 2 (2 * x) \<le> ?l\<close> (is ?thesis)
      using that Cons assms \<open>nat \<lceil>threshold\<rceil> \<ge> 2\<close>
      apply (subst (asm) Transcendental.log_le_iff)
      apply (simp_all add: x_def card_gt_0_iff Transcendental.powr_realpow)
      apply (subst (asm) mult_le_cancel_right_pos[
        of \<open>real <| nat \<lceil>threshold\<rceil>\<close>, symmetric])
      apply simp_all
      apply (simp only: Multiseries_Expansion.intyness_simps)
      by (smt (verit, ccfv_threshold) Num.of_nat_simps(5) One_nat_def Suc_1 nat_2 nat_le_eq_zle of_nat_le_iff of_nat_nat)

    have \<open>log 2 (2 * x) = 1 + log 2 x\<close> (is \<open>?L = _\<close>)
      apply (subst log_mult_pos)
      using assms \<open>nat \<lceil>threshold\<rceil> \<ge> 2\<close>
      by (simp_all add: log_mult_pos x_def Cons card_gt_0_iff)
    
    also have \<open>\<dots> \<le> log 2 4 + \<lfloor>log 2 x\<rfloor>\<close>
      by (smt (verit, best) Multiseries_Expansion.intyness_1 floor_eq_iff four_x_squared le_log_of_power log2_of_power_eq log_of_power_less one_power2 pos2 power_one_right)

    also have \<open>\<dots> = \<lfloor>log 2 <| 4 * x\<rfloor>\<close> (is \<open>_ = ?R\<close>)
      apply (subst log_mult_pos)
      using assms \<open>nat \<lceil>threshold\<rceil> \<ge> 2\<close>
      apply (simp_all add: log_mult_pos x_def Cons card_gt_0_iff field_simps)
      apply (simp only: Multiseries_Expansion.intyness_simps)
      by (metis of_int_numeral[of "num.Bit0 num.One"] numeral_Bit0_eq_double[of "num.Bit0 num.One"]
        of_int_add[of "2" "\<lfloor>log 2 (real (card (insert _ (set _))) / real_of_int \<lceil>12 * log 2 (real (8 + length _ * 8) / \<delta>) / (\<epsilon> * \<epsilon>)\<rceil>)\<rfloor>"]
        int_add_floor[of "2" "log 2 (real (card (insert _ (set _))) / real_of_int \<lceil>12 * log 2 (real (8 + length _ * 8) / \<delta>) / (\<epsilon> * \<epsilon>)\<rceil>)"] power2_eq_square[of \<epsilon>]
        power2_eq_square[of "2"] log2_of_power_eq[of "2\<^sup>2" "2"] Multiseries_Expansion.intyness_numeral[of "num.Bit0 (num.Bit0 (num.Bit1 num.One))"]
        Multiseries_Expansion.intyness_numeral[of "num.Bit0 num.One"])

    finally show ?thesis by simp
  qed

  moreover have
    \<open>2 ^ ?l * nat \<lceil>threshold\<rceil> \<le> 4 * card (set xs)\<close>
  proof -
    (* See comments on the context assms for how to discharge th is. *)
    have \<open>x \<ge> 1\<close> sorry

    then have \<open>2 ^ ?l \<le> 4 * x\<close>
      by (simp add: power_of_nat_log_le)

    with \<open>nat \<lceil>threshold\<rceil> \<ge> 2\<close>
    show ?thesis
      apply (subst (asm) mult_le_cancel_right_pos[
        of \<open>real <| nat \<lceil>threshold\<rceil>\<close>, symmetric])
      apply linarith
      apply (simp add: x_def field_simps split: if_splits)
      apply (simp only: Multiseries_Expansion.intyness_simps)
      by (smt (verit, best) Multiseries_Expansion.intyness_simps(2,5) of_nat_int_ceiling of_nat_le_iff)
  qed

  ultimately show ?thesis
    sorry
qed

end