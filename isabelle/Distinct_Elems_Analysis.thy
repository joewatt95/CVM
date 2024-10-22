section \<open> TODO \<close>
theory Distinct_Elems_Analysis

imports
  CVM.Distinct_Elems_Algo
  CVM.Distinct_Elems_No_Fail
  CVM.Distinct_Elems_Eager
  CVM.Distinct_Elems_Nondet
begin

context with_threshold
begin

context
  fixes \<epsilon> :: real
  assumes eps_pos : \<open>\<epsilon> > 0\<close>
begin

lemma estimate_distinct_error_bound:
  shows "
    \<P>(n in estimate_distinct xs.
      n |> fail_or_satisfies (beyond_eps_range_of_card \<epsilon> xs))
     \<le> real (length xs) / 2 ^ threshold + bar \<epsilon> thresh"
  (is "?L \<le> ?R")
proof -
  have "?L \<le> real (length xs) / 2 ^ threshold
    + \<P>(n in estimate_distinct_no_fail xs.
       n |> (beyond_eps_range_of_card \<epsilon> xs))"
    by (intro prob_estimate_distinct_fail_or_satisfies_le)

  moreover have
    "estimate_distinct_no_fail xs = (
      xs |> lazy_algorithm |> map_pmf compute_estimate)"
    unfolding estimate_distinct_no_fail_eq_lazy_algo ..
  
  (* moreover have
    "... = (
      fair_bernoulli_matrix n n
        |> map_pmf (
            (run_reader <| eager_algorithm xs)
              >>> compute_estimate))"
    sorry *)

  ultimately show ?thesis
    sorry
qed

end

end

end