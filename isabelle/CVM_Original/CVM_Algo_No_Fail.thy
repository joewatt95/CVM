section \<open> Analysis of algorithm TODO \<close>
theory CVM_Algo_No_Fail

imports
  CVM_Algo
begin

context cvm_algo_assms
begin

abbreviation \<open>step_no_fail \<equiv> \<lambda> x state. step_1 x state \<bind> step_2\<close>

abbreviation \<open>step_no_fail_spmf \<equiv> \<lambda> x. spmf_of_pmf <<< step_no_fail x\<close>

abbreviation \<open>run_steps_no_fail \<equiv> foldM_pmf step_no_fail\<close>

theorem
  "ord_spmf (=)
    (run_steps xs initial_state)
    (spmf_of_pmf (run_steps_no_fail xs initial_state))"
  sorry

theorem
  "prob_fail (run_steps xs initial_state) \<le> f ^ (threshold * length xs)"
  sorry

definition well_formed_state ::
  \<open>(nat \<Rightarrow> nat \<Rightarrow> bool) \<Rightarrow> ('a, 'b) state_scheme  \<Rightarrow> bool\<close> where
  (* (\<open>_ _ ok\<close> [20, 20] 60) *)
  \<open>well_formed_state \<equiv> \<lambda> R state. (
    let chi = state_chi state
    in finite chi \<and> R (card chi) threshold)\<close>

lemma well_formed_state_card_lt_thresholdD :
  assumes \<open>well_formed_state (<) state\<close>
  defines \<open>chi \<equiv> state_chi state\<close>
  shows
    \<open>card (Set.remove x chi) < threshold\<close> (is ?thesis_0)
    \<open>\<not> card (insert x chi) < threshold \<longleftrightarrow> card (insert x chi) = threshold\<close>
    (is ?thesis_1)
proof -
  note assms well_formed_state_def

  moreover from calculation show ?thesis_0
    by (metis card_Diff1_le dual_order.strict_trans2 remove_def)

  ultimately show ?thesis_1
    by (metis card.insert_remove linorder_neqE_nat not_less_eq remove_def)
qed

end

context algo_params_assms
begin

lemma initial_state_well_formed :
  \<open>well_formed_state (<) initial_state\<close>
  using threshold by (simp add: initial_state_def well_formed_state_def)

lemma step_preserves_well_formedness :
  \<open>\<turnstile>spmf \<lbrace>well_formed_state (<)\<rbrace> step x \<lbrace>well_formed_state (<)\<rbrace>\<close>
  (is \<open>PROP ?thesis'\<close>)
proof -
  have \<open>\<turnstile>spmf
    \<lbrace>well_formed_state (<)\<rbrace> spmf_of_pmf <<< step_1 x \<lbrace>well_formed_state (\<le>)\<rbrace>\<close>
    unfolding well_formed_state_def step_1_def Let_def map_pmf_def[symmetric]
    apply simp
    by (metis finite_insert insert_Diff_single less_or_eq_imp_le remove_def well_formed_state_card_lt_thresholdD(1,2) well_formed_state_def)

  moreover have
    \<open>\<turnstile>spmf \<lbrace>well_formed_state R\<rbrace> step_2 \<lbrace>well_formed_state (<)\<rbrace>\<close> for R
    unfolding well_formed_state_def step_2_def Let_def remove_def
    by (auto
      split: if_splits
      simp flip: bind_spmf_of_pmf simp add: set_bind_spmf)

  ultimately show \<open>PROP ?thesis'\<close>
    unfolding step_def
    by (metis (mono_tags, lifting) AE_measure_spmf_iff UN_E bind_UNION o_def set_bind_spmf)
qed

(* TODO: tidy *)
lemma prob_fail_step_le :
  assumes \<open>well_formed_state (<) state\<close>
  shows \<open>prob_fail (step x state) \<le> f ^ threshold\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  let ?chi = \<open>insert x <| state_chi state\<close>

  have \<open>?L = measure_pmf.expectation (step_1 x state) (prob_fail <<< step_2)\<close>
    unfolding step_def pmf_bind_spmf_None by simp

  text\<open>step_2 fails after step_1 has run iff:
    1. We first sample \<top> from step_1 with probability `f ^ state_k state`,
      inserting the new element into `chi`, yielding ?chi.
    2. Doing the causes ?chi to hit the threshold.
    3. We sample a characteristic function `keep_in_chi` of a subset of ?chi
      that evaluates to \<top> everywhere on ?chi.\<close>
  also have \<open>\<dots> =
    f ^ state_k state * of_bool (card ?chi = threshold) *
    measure_pmf.expectation (prod_pmf ?chi (\<lambda> _. bernoulli_pmf f))
      (\<lambda> keep_in_chi. \<Prod> x' \<in> ?chi. of_bool (keep_in_chi x'))\<close>
    (is \<open>_ = _ * _ * measure_pmf.expectation _ ?prob_fail_given_keep_in_chi\<close>)
  proof -
    note assms

    moreover from calculation have
      \<open>?prob_fail_given_keep_in_chi keep_in_chi =
      prob_fail (
        let chi = Set.filter keep_in_chi ?chi
        in if card chi < threshold
          then return_spmf
            \<lparr>state_k = state_k (state\<lparr>state_chi := ?chi\<rparr>) + 1, state_chi = chi\<rparr>
          else fail_spmf)\<close>
      if \<open>card ?chi = threshold\<close> for keep_in_chi
      using that
      apply (simp add: well_formed_state_def Let_def)
      by (smt (verit, best) card_mono card_seteq finite.insertI finite_filter insert_iff member_filter of_bool_eq(2) prod.neutral subsetI verit_comp_simplify(3))

    ultimately show ?thesis
      using f well_formed_state_card_lt_thresholdD
      unfolding step_1_def step_2_def well_formed_state_def map_pmf_def[symmetric] Let_def
      by (fastforce
        intro!: integral_cong_AE simp add: power_le_one pmf_bind)
  qed
  
  text\<open>Note now that the probability of keep_in_chi evaluating to \<top> on ?chi
    is = f ^ threshold.\<close>
  also from f assms have \<open>\<dots> =
    f ^ state_k state * of_bool (card ?chi = threshold) * f ^ threshold\<close>
    unfolding well_formed_state_def Let_def
    apply (subst expectation_prod_Pi_pmf)
    by (auto simp add: integrable_measure_pmf_finite card.insert_remove)

  finally show ?thesis using f by (simp add: power_le_one)
qed

lemma prob_fail_estimate_size_le :
  \<open>prob_fail (estimate_distinct xs) \<le> length xs * f ^ threshold\<close>
  unfolding estimate_distinct_def run_steps_then_estimate_def
  apply simp
  by (metis algo_params_assms.prob_fail_step_le algo_params_assms.step_preserves_well_formedness algo_params_assms_axioms initial_state_well_formed prob_fail_foldM_spmf_le)

lemma step_ord_spmf_eq :
  \<open>step x state \<sqsubseteq> spmf_of_pmf (step_no_fail x state)\<close>
  by (fastforce
    intro: ord_spmf_bind_reflI
    simp flip: bind_spmf_of_pmf
    simp add:
      step_1_no_fail_def step_2_no_fail_def step_def Let_def
      spmf_of_pmf_def map_bind_pmf)

lemma estimate_distinct_ord_spmf_eq :
  \<open>estimate_distinct xs \<sqsubseteq> spmf_of_pmf (estimate_distinct_no_fail xs)\<close>
  apply (simp
    flip: map_spmf_of_pmf
    add:
      estimate_distinct_def estimate_distinct_no_fail_def
      run_steps_then_estimate_def ord_spmf_map_spmf)
  by (metis (mono_tags, lifting) foldM_spmf_of_pmf_eq foldM_spmf_ord_spmf_eq_of_ord_spmf_eq ord_spmf_mono step_ord_spmf_eq)

(* Think of P as event that `estimate` is the wrong count *)
theorem prob_estimate_distinct_is_None_or_pred_le :
  \<open>\<P>(estimate in estimate_distinct xs. estimate |> fails_oris_None_or_pred
  \<le> real (length xs) / 2 ^ threshold
    + \<P>(estimate in estimate_distinct_no_fail xs. P estimate)\<close>
  by (smt (verit, del_insts) Collect_cong estimate_distinct_ord_spmf_eq measure_spmf_spmf_of_pmf prob_fail_estimate_size_le prob_is_None_or_pred_eq_prob_fail_plus_prob prob_le_prob_of_ord_spmf_eq)

end

end