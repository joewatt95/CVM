theory CVM

imports
  CVM.Basic_Props
  CVM.Final_Props

begin

context basic_algo
begin

lemma
  fixes xs k
  defines
    \<open>R final_state estimated_size' \<equiv>
      k = state_k final_state
        \<longrightarrow> (state_estimated_size final_state :: real) = estimated_size'\<close>
  shows
    \<open>rel_spmf R
      (estimate_distinct False xs) <|
      spmf_of_pmf (Final_Algo.estimate_distinct k <| set xs)\<close>

  apply (simp add: estimate_distinct_eq_binomial)
  apply (auto
    simp add:
      assms estimate_distinct_def Final_Algo.estimate_distinct_def
      run_steps_def step_def result_def initial_state_def
      map_spmf_of_pmf[symmetric] bind_spmf_of_pmf[symmetric]
      spmf_rel_map Set.filter_def state.extend_def Let_def Set.remove_def
    simp del: map_spmf_of_pmf bind_spmf_of_pmf)

  sorry

lemma
  fixes
    P :: \<open>real \<Rightarrow> bool\<close>
  shows
    \<open>\<P>(state in estimate_distinct_pmf xs.
        P (state_k state) \<and> k = state_k state)
      = \<P>(estimated_size in Final_Algo.estimate_distinct k <| set xs.
            P estimated_size)\<close>

  sorry

(* lemma
  fixes P :: \<open>real \<Rightarrow> bool\<close>
  shows
    \<open>\<P>(state in cond_pmf (estimate_distinct_pmf xs) {final_state. k = state_k final_state}.
        P (state_k state))
      \<le> \<P>(estimated_size in Final_Algo.estimate_distinct k (set xs). P estimated_size)\<close>

  sorry *)

lemma
  fixes k xs
  defines
    \<open>estimate_distinct_k \<equiv>
      cond_spmf
        (estimate_distinct False xs)
        {final_state. k = state_k final_state}\<close>
  shows
    \<open>rel_spmf (=)
      (map_spmf state_k estimate_distinct_k) <|
      spmf_of_pmf <| Final_Algo.estimate_distinct k <| set xs\<close>

  unfolding assms
  apply (auto
    simp add:
      estimate_distinct_eq_binomial
      estimate_distinct_def run_steps_def result_def state.extend_def
      initial_state_def
      map_spmf_of_pmf[symmetric] binomial_pmf_0
      spmf_rel_eq[symmetric] spmf_rel_map
    simp del: map_spmf_of_pmf
    )

  sorry

end

end