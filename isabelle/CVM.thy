theory CVM

imports
  CVM.Basic_Props
  CVM.Final_Props

begin

context basic_algo
begin

lemma test0 :
  fixes xs k
  defines
    \<open>R final_state estimated_size' \<equiv>
      k = state_k final_state
        \<longrightarrow> (state_estimated_size final_state :: real) = estimated_size'\<close>
  shows
    \<open>rel_pmf R
      (estimate_distinct_pmf xs)
      (Final_Algo.estimate_distinct k <| set xs)\<close>

  sorry

lemma test1 :
  fixes
    P :: \<open>real \<Rightarrow> bool\<close>
  shows
    \<open>\<P>(state in estimate_distinct_pmf xs.
        P (state_k state) \<and> k = state_k state)
      = \<P>(estimated_size in Final_Algo.estimate_distinct k <| set xs.
            P estimated_size)\<close>

  apply simp
  sorry

(* find_theorems "measure_pmf.prob ?p ?A \<le> measure_pmf.prob ?q ?A"

thm pmf.rel_mono *)

lemma test2 :
  fixes P :: \<open>real \<Rightarrow> bool\<close>
  shows
    \<open>\<P>(state in cond_pmf (estimate_distinct_pmf xs) {final_state. k = state_k final_state}.
        P (state_k state))
      \<le> \<P>(estimated_size in Final_Algo.estimate_distinct k (set xs). P estimated_size)\<close>

  apply simp
  sorry

lemma test3 :
  \<open>map_pmf state_k (cond_pmf (estimate_distinct_pmf xs) {final_state. k = state_k final_state})
    = Final_Algo.estimate_distinct k (set xs)\<close>

  sorry

end

end