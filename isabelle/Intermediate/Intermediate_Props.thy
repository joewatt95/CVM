theory Intermediate_Props

imports
  CVM.Intermediate_Algo
  CVM.Basic_Props
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

locale intermediate_algo = basic_algo
begin

lemma
  defines \<open>R \<equiv> \<lambda> state chis.
    state_chi state = chis ! state_k state\<close>
  shows \<open>\<turnstile> \<lbrace>R\<rbrace> \<langle>step False x | (spmf_of_pmf <<< Intermediate_Algo.step x)\<rangle> \<lbrace>R\<rbrace>\<close>

  sorry

end

end