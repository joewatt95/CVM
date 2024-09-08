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
  CVM.Utils_SPMF
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

locale props_basic = props_approx_algo + algo_basic
begin

context includes pattern_aliases
begin

context includes monad_normalisation
begin

lemma prob_fail_step :
  fixes
    x :: 'a and
    state :: \<open>'a state\<close>
  shows \<open>prob_fail (step x state) \<le> 2 powr threshold\<close>
proof (cases state)
  case (fields p chi)

  show ?thesis
    using local.fields
    apply (auto simp add: prob_fail_def pmf_bind)
    apply (subst integral_bernoulli_pmf)
    apply auto
    sorry

qed

lemma prob_fail_estimate_size :
  fixes xs :: \<open>'a list\<close>
  shows \<open>prob_fail (estimate_size xs) \<le> length xs * 2 powr threshold\<close>
proof -
  have \<open>prob_fail (estimate_size xs) = prob_fail (run_steps initial_state xs)\<close>
    by (simp add: estimate_size_def prob_fail_def pmf_None_eq_weight_spmf)

  then show ?thesis
    by (auto
        intro!: foldM_spmf.prob_fail_foldM_spmf prob_fail_step
        simp add: run_steps_def)
qed

end

end

end

end