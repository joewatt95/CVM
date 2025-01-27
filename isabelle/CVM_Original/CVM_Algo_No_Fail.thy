section \<open> Analysis of algorithm TODO \<close>
theory CVM_Algo_No_Fail

imports
  CVM_Algo
  Utils_SPMF_Hoare
  Utils_SPMF_Relational

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
    simp add: AE_measure_pmf_iff)

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

  also from assms step_2_finite_support_after_step_1 step_1_finite_support
  have \<open>\<dots> =
    measure_pmf.expectation (step_1 x state)
      (\<lambda> state.
        measure_pmf.expectation (step_2 state)
        (prob_fail <<< step_3))\<close>
    (is \<open>_ = measure_pmf.expectation _ ?prob_fail_step_3_after_step_2\<close>)
    apply (subst integral_bind_pmf)
    by (fastforce simp add: AE_measure_pmf_iff)+

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

      also from that have \<open>\<dots> =
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

lemma prob_fail_run_steps_le :
  \<open>prob_fail (run_steps xs initial_state) \<le> length xs * f ^ threshold\<close>
  by (metis prob_fail_foldM_spmf_le prob_fail_step_le step_preserves_well_formedness wf_state_initial_state)

lemma step_le_step_no_fail :
  \<open>step x state \<sqsubseteq>\<^bsub>(=)\<^esub> spmf_of_pmf (step_no_fail x state)\<close>
  apply (simp add: step_def step_3_def spmf_of_pmf_bind)
  by (smt (verit) bind_return_spmf ord_spmf_None ord_spmf_bind_reflI spmf.leq_refl)

lemma run_steps_le_run_steps_no_fail :
  \<open>run_steps xs state \<sqsubseteq>\<^bsub>(=)\<^esub> spmf_of_pmf (run_steps_no_fail xs state)\<close>
  unfolding foldM_spmf_of_pmf_eq[symmetric]
  by (blast intro: foldM_spmf_ord_spmf_eq_of_ord_spmf_eq step_le_step_no_fail)

(* Think of P as event that `estimate` is the wrong count *)
theorem prob_run_steps_is_None_or_pred_le :
  \<open>\<P>(state in run_steps xs initial_state. state |> is_None_or_pred P)
  \<le> real (length xs) * f ^ threshold +
    \<P>(state in run_steps_no_fail xs initial_state. P state)\<close>
  (is \<open>?L is_None_or_pred \<le> ?R\<close>)
proof -
  have \<open>?L is_None_or_pred =
    prob_fail (run_steps xs initial_state) + ?L is_Some_and_pred\<close>
    by (metis measure_spmf_eq_measure_pmf_is_Some_and_pred prob_is_None_or_pred_eq_prob_fail_plus_prob)

  with
    prob_fail_run_steps_le
    prob_measure_spmf_le_of_ord_spmf[OF run_steps_le_run_steps_no_fail]
  show ?thesis
    by (smt (verit, del_insts) Collect_cong measure_spmf_eq_measure_pmf_is_Some_and_pred measure_spmf_spmf_of_pmf)
qed

end

end