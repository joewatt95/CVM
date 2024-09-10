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

fun well_formed_state :: \<open>'a state \<Rightarrow> bool\<close>
  (\<open>\<turnstile> _ ok\<close> [20] 60) where
  \<open>\<turnstile> \<lparr>state_p = p, state_chi = chi\<rparr> ok =
    (p \<in> {0 <.. 1} \<and> card chi < threshold)\<close>

context includes monad_normalisation
begin

lemma prob_fail_step_le :
  fixes
    x :: 'a and
    state :: \<open>'a state\<close>
  shows \<open>prob_fail (step x state) \<le> 2 powr threshold\<close>
proof (cases state)
  case (fields p chi)
  (*
  0 \<le> p \<le> 1 is required to simp using integral_bernoulli_pmf
  *)
  have \<open>\<turnstile> state ok\<close> sorry

  then show ?thesis
    apply (auto simp add: prob_fail_def pmf_bind)
    (* apply (subst expectation_prod_Pi_pmf) *)
    sorry

qed

lemma prob_fail_estimate_size_le :
  fixes xs :: \<open>'a list\<close>
  shows \<open>prob_fail (estimate_size xs) \<le> length xs * 2 powr threshold\<close>
proof -
  have \<open>prob_fail (estimate_size xs) = prob_fail (run_steps initial_state xs)\<close>
    by (simp add: estimate_size_def prob_fail_def pmf_None_eq_weight_spmf)

  then show ?thesis
    by (auto
        intro!: foldM_spmf.prob_fail_foldM_spmf_le prob_fail_step_le
        simp add: run_steps_def)
qed

end

end

end

end