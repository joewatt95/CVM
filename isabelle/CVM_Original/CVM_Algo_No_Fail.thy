section \<open> Analysis of algorithm TODO \<close>
theory CVM_Algo_No_Fail

imports
  CVM_Algo
  Utils_SPMF_Hoare

begin

context cvm_algo_assms
begin

abbreviation \<open>step_no_fail \<equiv> \<lambda> x state. step_1 x state \<bind> step_2\<close>

abbreviation \<open>step_no_fail_spmf \<equiv> \<lambda> x. spmf_of_pmf <<< step_no_fail x\<close>

abbreviation \<open>run_steps_no_fail \<equiv> foldM_pmf step_no_fail\<close>

abbreviation \<open>wf_state \<equiv> \<lambda> state. finite (state_chi state)\<close>

(* not convinced this is needed, at least here...*)
(* definition
  \<open>wf_state \<equiv> \<lambda> R state. (
    let chi = state_chi state
    in finite chi \<and> R (card chi) threshold)\<close> *)

lemma wf_state_initial_state :
  \<open>wf_state initial_state\<close>
  by (simp add: initial_state_def)

lemma step_1_preserves_well_formedness :
  \<open>\<turnstile>pmf \<lbrakk>wf_state\<rbrakk> step_1 x \<lbrakk>wf_state\<rbrakk>\<close>
  unfolding step_1_def' by (simp add: AE_measure_pmf_iff remove_def)

lemma step_2_preserves_well_formedness :
  \<open>\<turnstile>pmf \<lbrakk>wf_state\<rbrakk> step_2 \<lbrakk>wf_state\<rbrakk>\<close>
  unfolding step_2_def' by (simp add: AE_measure_pmf_iff)

lemma step_preserves_well_formedness :
  \<open>\<turnstile>spmf \<lbrace>wf_state\<rbrace> step x \<lbrace>wf_state\<rbrace>\<close>
  unfolding step_def step_3_def
  using step_1_preserves_well_formedness step_2_preserves_well_formedness
  by (force
    split: if_splits
    simp flip: bind_spmf_of_pmf
    simp add: set_bind_spmf AE_measure_pmf_iff)

lemma step_1_finite_support :
  \<open>finite <| set_pmf <| step_1 x state\<close>
  unfolding step_1_def' by simp

lemma step_2_finite_support :
  assumes \<open>wf_state state\<close>
  shows \<open>finite <| set_pmf <| step_2 state\<close>
  using assms
  unfolding step_2_def' by (simp add: set_prod_pmf finite_PiE)

lemma step_2_finite_support_after_step_1 :
  \<open>\<turnstile>pmf \<lbrakk>wf_state\<rbrakk> step_1 x \<lbrakk>(\<lambda> state. finite (set_pmf <| step_2 state))\<rbrakk>\<close>
  by (metis (no_types, lifting) eventually_mono step_1_preserves_well_formedness step_2_finite_support)

lemma prob_fail_step_le :
  assumes \<open>wf_state state\<close>
  shows \<open>prob_fail (step x state) \<le> f ^ threshold\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  have \<open>?L =
    measure_pmf.expectation (step_1 x state \<bind> step_2) (prob_fail <<< step_3)\<close>
    unfolding step_def pmf_bind_spmf_None by simp

  also from assms step_2_finite_support_after_step_1 have \<open>\<dots> =
    measure_pmf.expectation (step_1 x state)
      (\<lambda> state.
        measure_pmf.expectation (step_2 state)
        (prob_fail <<< step_3))\<close>
    (is \<open>_ = measure_pmf.expectation _ ?prob_fail_step_3_after_step_2\<close>)
    apply (subst integral_bind_pmf)
    by (fastforce simp add: AE_measure_pmf_iff step_1_finite_support)+

  also have \<open>\<dots> \<le> measure_pmf.expectation (step_1 x state) (\<lambda> _. f ^ threshold)\<close>
  proof -
    have
      \<open>?prob_fail_step_3_after_step_2 state \<le> f ^ threshold\<close> (is \<open>?L' \<le> ?R'\<close>)
      if \<open>wf_state state\<close> for state :: \<open>'a state\<close>
    proof -
      let ?chi = \<open>state_chi state\<close>

      have \<open>?L' =
        of_bool (card ?chi = threshold) *
        measure_pmf.expectation (prod_pmf ?chi (\<lambda> _. bernoulli_pmf f))
          (\<lambda> keep_in_chi.
            of_bool (card (Set.filter keep_in_chi ?chi) = card ?chi))\<close>
        by (auto intro!: integral_cong_AE simp add: step_2_def' step_3_def)

      also from assms that have \<open>\<dots> =
        of_bool (card ?chi = threshold) *
        measure_pmf.expectation (prod_pmf ?chi (\<lambda> _. bernoulli_pmf f))
          (\<lambda> keep_in_chi. \<Prod> x \<in> ?chi. of_bool (keep_in_chi x))\<close>
        by (auto
          intro!: integral_cong_AE
          simp add: AE_measure_pmf_iff finset_card_filter_eq_iff_Ball)

      also have \<open>\<dots> \<le> ?R'\<close>
        using assms that f
        apply (subst expectation_prod_Pi_pmf)
        by (simp_all add: integrable_measure_pmf_finite)

      finally show ?thesis .
    qed

    with assms step_1_preserves_well_formedness show ?thesis
      apply (intro integral_mono_AE)
      by (fastforce simp add: integrable_measure_pmf_finite step_1_finite_support AE_measure_pmf_iff)+
  qed

  finally show ?thesis by simp
qed

theorem
  "ord_spmf (=)
    (run_steps xs initial_state)
    (spmf_of_pmf (run_steps_no_fail xs initial_state))"
  sorry

theorem
  "prob_fail (run_steps xs initial_state) \<le> f ^ (threshold * length xs)"
  sorry

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
    sorry
    (* by (metis card_Diff1_le dual_order.strict_trans2 remove_def) *)

  ultimately show ?thesis_1
    sorry
    (* by (metis card.insert_remove linorder_neqE_nat not_less_eq remove_def) *)
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
    sorry
    (* by (metis (mono_tags, lifting) AE_measure_spmf_iff UN_E bind_UNION o_def set_bind_spmf) *)
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