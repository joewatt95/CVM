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
  defines
    \<open>R \<equiv> \<lambda> index state chis. (
      let
        k = state_k state;
        chi = state_chi state
      in k \<le> index \<and> length chis = n
        \<and> chi = chis ! k)\<close>
  shows
    \<open>\<turnstile> \<lbrace>(\<lambda> state chis. index < n \<and> R index state chis)\<rbrace>
      \<langle>step False x | (spmf_of_pmf <<< Intermediate_Algo.step x)\<rangle>
      \<lbrace>R (index + 1)\<rbrace>\<close>
    (is \<open>\<turnstile> \<lbrace>?R'\<rbrace> \<langle>?p | ?q\<rangle> \<lbrace>_\<rbrace>\<close>)
proof -
  {
    fix state chis

    assume \<open>?R' state chis\<close>

    then have \<open>rel_spmf (R <| index + 1) (?p state) <| ?q chis\<close>
      apply (intro rel_spmfI[where ?pq = \<open>pair_spmf (?p state) <| ?q chis\<close>])
      unfolding step_def
      apply (auto
        elim!: bind_elim
        split: if_splits
        simp del: bind_spmf_of_pmf
        simp add:
          Intermediate_Algo.step_def
          map_index_def
          bind_spmf_of_pmf[symmetric]
          map_pmf_def[symmetric]
          Let_def)

      using assms apply simp

      sorry
  }

  show ?thesis sorry

  (* unfolding step_def
  apply (auto 
    simp add:
      Intermediate_Algo.step_def relational_hoare_triple_def
      map_pmf_def[symmetric]
      Let_def)

  apply (intro rel_spmfI)

  sorry *)
qed

find_theorems "rel_spmf _ (spmf_of_pmf _)"

end

end