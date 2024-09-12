theory Basic_Props

imports
  HOL.Power
  "HOL-Probability.Product_PMF"
  "HOL-Probability.Hoeffding"
  Monad_Normalisation.Monad_Normalisation
  CVM.Basic_Algo
  CVM.Utils_Approx_Algo
  CVM.Utils_Function
  CVM.Utils_PMF
  CVM.Utils_SPMF_Hoare
  CVM.Utils_Real

begin

sledgehammer_params [
  (* verbose = true, *)
  minimize = true,
  preplay_timeout = 15,
  timeout = 60,
  max_facts = smart,
  provers = "
    cvc4 z3 verit
    e vampire spass
  "
]

locale props_basic = approx_algo + basic_algo
begin

context includes pattern_aliases
begin

context includes monad_normalisation
begin

definition well_formed_state :: \<open>'a state \<Rightarrow> bool\<close>
  (\<open>_ ok\<close> [20] 60) where
  \<open>state ok \<equiv> (
    let chi = state_chi state
    in finite chi \<and> card chi < threshold)\<close>

lemma initial_state_well_formed :
  assumes \<open>card (state_chi initial_state) < threshold\<close>
  shows \<open>initial_state ok\<close>

  using assms by (simp add: initial_state_def well_formed_state_def)

lemma step_preserves_well_formedness :
  fixes x :: 'a
  shows \<open>\<turnstile> \<lbrace>well_formed_state\<rbrace> step x \<lbrace>well_formed_state\<rbrace>\<close>

  unfolding step_def
  apply (simp del: bind_spmf_of_pmf)
  apply (rule seq'[where ?Q = \<open>\<lblot>True\<rblot>\<close>])
  by (auto
      intro!: hoare_triple_intro
      split: if_splits
      simp add: fail_spmf_def in_set_spmf well_formed_state_def remove_def)

lemma prob_fail_step_le :
  fixes
    x :: 'a and
    state :: \<open>'a state\<close>
  assumes \<open>state ok\<close>
  shows \<open>prob_fail (step x state) \<le> 2 powr threshold\<close>

  by (metis assms ge_one_powr_ge_zero less_eq_real_def nle_le numeral_le_one_iff of_nat_0_le_iff order.trans pmf_le_1 prob_fail_def semiring_norm(69) well_formed_state_def) 

lemma prob_fail_estimate_size_le :
  fixes xs :: \<open>'a list\<close>
  assumes \<open>card (state_chi initial_state) < threshold\<close>
  shows \<open>prob_fail (estimate_size xs) \<le> length xs * 2 powr threshold\<close>
proof -
  have \<open>prob_fail (estimate_size xs) = prob_fail (run_steps initial_state xs)\<close>
    by (simp add: estimate_size_def prob_fail_def pmf_None_eq_weight_spmf)

  then show ?thesis
    using assms
    by (auto
        intro!:
          prob_fail_foldM_spmf_le initial_state_well_formed
          prob_fail_step_le step_preserves_well_formedness
        simp add: run_steps_def)
qed

end

end

end

end