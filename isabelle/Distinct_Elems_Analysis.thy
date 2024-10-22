section \<open> TODO \<close>
theory Distinct_Elems_Analysis

imports
  CVM.Utils_Approx_Algo
  CVM.Distinct_Elems_Algo
  CVM.Distinct_Elems_No_Fail
  CVM.Distinct_Elems_Eager
begin

context with_threshold
begin

context
  fixes \<epsilon> :: real
  assumes eps_pos : \<open>\<epsilon> > 0\<close>
begin

definition eps_approxs_F0 :: "'a set \<Rightarrow> nat \<Rightarrow> bool" where
  "eps_approxs_F0 X n \<equiv> real n \<approx>[\<epsilon>] card X"

lemma estimate_distinct_error_bound:
  shows "
    \<P>(n in estimate_distinct xs.
      n |> fail_or_satisfies (eps_approxs_F0 <| set xs))
     \<le> real (length xs) / 2 ^ threshold + bar \<epsilon> thresh"
  (is "?L \<le> ?R")
proof -
  
  have "?L \<le> real (length xs) / 2 ^ threshold
    + \<P>(n in estimate_distinct_no_fail xs.
       n |> (eps_approxs_F0 <| set xs))"
    by (intro prob_estimate_distinct_fail_or_satisfies_le)

  moreover have
    "estimate_distinct_no_fail xs =
    map_pmf get_estimate (lazy_algorithm xs)"
    sorry
  show ?thesis
    sorry
qed

end

end

end