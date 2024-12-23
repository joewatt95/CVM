theory Basic_Props_With_Failure

imports
  HOL.Power
  "HOL-Probability.Product_PMF"
  "HOL-Probability.Hoeffding"
  CVM.Basic_Algo
  CVM.Utils_Approx_Algo
  CVM.Utils_SPMF_Hoare

begin

sledgehammer_params [
  (* verbose *)
  minimize = true,
  preplay_timeout = 15,
  timeout = 60,
  max_facts = smart,
  provers = "
    cvc4 z3 verit
    e vampire spass
  "
]

context basic_algo
begin

context
  assumes threshold_pos : \<open>threshold > 0\<close>
begin

definition well_formed_state :: \<open>('a, 'b) state_scheme \<Rightarrow> bool\<close>
  (\<open>_ ok\<close> [20] 60) where
  \<open>state ok \<equiv> (
    let chi = state_chi state
    in finite chi \<and> card chi < threshold)\<close>

lemma initial_state_well_formed :
  \<open>initial_state ok\<close>

  using threshold_pos by (simp add: initial_state_def well_formed_state_def)

lemma step_preserves_well_formedness :
  \<open>\<turnstile> \<lbrace>well_formed_state\<rbrace> step Fail x \<lbrace>well_formed_state\<rbrace>\<close>

  unfolding step_def
  apply (simp del: bind_spmf_of_pmf add: bind_spmf_of_pmf[symmetric] Let_def)
  apply (rule seq')
  by (auto
      intro!: hoare_triple_intro
      split: if_splits
      simp add: in_set_spmf well_formed_state_def remove_def Let_def)

lemma prob_fail_step_le :
  fixes
    x :: 'a and
    state :: \<open>'a state\<close>
  assumes \<open>state ok\<close>
  shows \<open>prob_fail (step Fail x state) \<le> 2 powr threshold\<close>

  by (metis assms ge_one_powr_ge_zero less_eq_real_def nle_le numeral_le_one_iff of_nat_0_le_iff order.trans pmf_le_1 prob_fail_def semiring_norm(69) well_formed_state_def) 

lemma prob_fail_estimate_size_le :
  \<open>prob_fail (estimate_distinct Fail xs) \<le> length xs * 2 powr threshold\<close>
proof -
  have
    \<open>prob_fail (estimate_distinct Fail xs)
      = prob_fail (run_steps Fail initial_state xs)\<close>
    by (simp add: estimate_distinct_def prob_fail_def pmf_None_eq_weight_spmf)

  then show ?thesis
    using threshold_pos
    by (auto
        intro:
          prob_fail_foldM_spmf_le initial_state_well_formed
          prob_fail_step_le step_preserves_well_formedness
        simp add: run_steps_def)
qed

end

end

end