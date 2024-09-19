theory Basic_Props

imports
  CVM.Basic_Props_With_Failure
  CVM.Basic_Props_Without_Failure
  CVM.Utils_SPMF_Rel

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

lemma step_with_fail_ord_spmf_eq_step_without_fail :
  \<open>ord_spmf (=) (step True x state) <| step False x state\<close>

  by (auto
      intro!: ord_spmf_bind_reflI
      simp del: bind_spmf_of_pmf
      simp add:
        step_def fail_spmf_def
        bind_spmf_of_pmf[symmetric] Let_def)

lemma
  \<open>ord_spmf (=) (estimate_distinct True xs) <| estimate_distinct False xs\<close>

  using step_with_fail_ord_spmf_eq_step_without_fail
  apply (induction xs)

  apply (auto
    intro!: ord_spmf_bindI
    simp add:
      estimate_distinct_def run_steps_def
      ord_spmf_map_spmf12)

  sorry

lemma prob_step_with_failure_le_step_without_failure :
  fixes P x state
  defines
    \<open>prob fail \<equiv>
      \<P>(state' in measure_spmf <| step fail x state. P state')\<close>
  shows \<open>prob True \<le> prob False\<close>

  by (simp add: prob_le_prob_of_ord_spmf_eq step_with_fail_ord_spmf_eq_step_without_fail assms)

lemma
  fixes P xs
  defines
    \<open>prob fail \<equiv>
      \<P>(state' in measure_spmf <| estimate_distinct fail xs. P state')\<close>
  shows \<open>prob True \<le> prob False\<close>

  sorry

end

end