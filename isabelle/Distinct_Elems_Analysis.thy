section \<open> TODO \<close>
theory Distinct_Elems_Analysis

imports
  Distinct_Elems_Algo
  Distinct_Elems_No_Fail
  Distinct_Elems_Eager
begin

context with_threshold
begin

term "fail_or_satisfies"

definition eps_F0_approx :: "real \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> bool" where
  "eps_F0_approx (\<epsilon>::real) X n \<longleftrightarrow>
    n \<in> {(1-\<epsilon>)*real (card X)..(1+\<epsilon>)*real (card X)} "

lemma estimate_distinct_error_bound:
  assumes "\<epsilon> > 0"
  shows "
    \<P>(n in estimate_distinct xs. n
      |> fail_or_satisfies
        (eps_F0_approx \<epsilon> (set xs)))
     \<le> real (length xs) / 2 ^ threshold +
        bar \<epsilon> thresh"
  (is "?L \<le> ?R")
proof -
  
  have "?L \<le> real (length xs) / 2 ^ threshold
    + \<P>(n in estimate_distinct_no_fail xs.
       n |> (eps_F0_approx \<epsilon> (set xs)))"
    by (intro prob_estimate_distinct_fail_or_satisfies_le)

  moreover have
    "estimate_distinct_no_fail xs =
    map_pmf get_estimate (lazy_algorithm xs)"
    sorry
  show ?thesis
    sorry
qed

end