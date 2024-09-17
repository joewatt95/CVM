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

abbreviation step_with_failure where
  \<open>step_with_failure \<equiv> step fail\<close>

abbreviation step_without_failure where
  \<open>step_without_failure \<equiv> step dont_fail\<close>

lemma test :
  assumes \<open>state ok\<close>
  shows \<open>step_with_failure x state = step_without_failure x state\<close>

  using assms
  apply (auto
    intro!: spmf_eqI
    simp del: bind_spmf_of_pmf
    simp add:
      spmf_bind
      bind_spmf_of_pmf[symmetric] fail dont_fail step_def well_formed_state_def
      Let_def)

  (* apply (simp
    del: bind_spmf_of_pmf
    add: bind_spmf_of_pmf[symmetric] step_def Let_def)
  apply (intro spmf_eqI)
  apply (simp only: spmf_bind)
  apply auto
  apply (simp_all
    del: bind_spmf_of_pmf
    add: bind_spmf_of_pmf[symmetric] Let_def)
  apply (simp_all only: spmf_bind)
  apply auto *)

  sorry

(* 
lemma step_equiv_up_to_failure :
  fixes P x state
  shows \<open>\<turnstile> \<lbrakk>P\<rbrakk>(step_with_failure x state) \<simeq> \<lbrakk>P\<rbrakk>(step_without_failure x state)\<close>

  using fail dont_fail
  apply (simp
    del: bind_spmf_of_pmf
    add: bind_spmf_of_pmf[symmetric] equiv_up_to_failure_def step_def Let_def)
  apply (intro rel_spmf_bindI)
  apply auto
  apply (intro rel_pmf_reflI)
  apply auto
  apply (simp_all
    del: bind_spmf_of_pmf
    add: bind_spmf_of_pmf[symmetric] equiv_up_to_failure_def step_def Let_def)
  apply (intro rel_spmf_bindI)
  apply auto
  apply (intro rel_pmf_reflI)
  apply (auto simp add: fail_spmf_def)

  sorry *)

(* definition rel where
  \<open>rel state state' \<equiv> 0\<close> *)

(* lemma test :
  \<open>rel_spmf <| \<lambda>\<close> *)

end

end

end