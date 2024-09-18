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

context
  fixes
    fail :: bool and
    dont_fail :: bool
  assumes
    fail : \<open>fail\<close> and
    dont_fail : \<open>\<not> dont_fail\<close>
begin

abbreviation step_with_failure ::
  \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step_with_failure \<equiv> step fail\<close>

abbreviation step_without_failure ::
  \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step_without_failure \<equiv> step dont_fail\<close>

lemma prob_step_with_failure_le_step_without_failure :
  fixes P x state
  defines \<open>prob f \<equiv> \<P>(state' in measure_spmf <| f x state. P state')\<close>
  shows \<open>prob step_with_failure \<le> prob step_without_failure\<close>
proof -
  have \<open>ord_spmf (=) (step_with_failure x state) (step_without_failure x state)\<close> 
    by (auto
        intro!: ord_spmf_bind_reflI
        simp del: bind_spmf_of_pmf
        simp add:
          fail dont_fail step_def fail_spmf_def
          bind_spmf_of_pmf[symmetric] Let_def)

  then show ?thesis using prob_le_prob_of_ord_spmf_eq assms by simp
qed

end

end

end