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
  fixes index n
  defines \<open>R \<equiv> \<lambda> index state chis. (
    let
      k = state_k state;
      chi = state_chi state
    in k \<le> index \<and> length chis = n
      \<and> chi = chis ! k)\<close>
  shows
    \<open>\<turnstile> \<lbrace>(\<lambda> val val'. index < n \<and> R index val val')\<rbrace>
      \<langle>step False x | (spmf_of_pmf <<< Intermediate_Algo.step x)\<rangle>
      \<lbrace>R (index + 1)\<rbrace>\<close>

  sorry

end

end