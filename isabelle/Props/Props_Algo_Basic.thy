theory Props_Algo_Basic

imports
  HOL.Power
  "HOL-Probability.Product_PMF"
  "HOL-Probability.Hoeffding"
  CVM.Algo_Basic
  CVM.Props_Approx_Algo
  CVM.Utils_Function
  CVM.Utils_PMF
  CVM.Utils_SPMF
  CVM.Utils_Real

begin

sledgehammer_params [
  (* verbose = true, *)
  minimize = true,
  preplay_timeout = 15,
  timeout = 60,
  max_facts = smart,
  provers = "
    cvc4 z3 verit
    e vampire spass
  "
]

locale props_basic = props_approx_algo + algo_basic
begin

context includes pattern_aliases
begin

(* lemma prob_fail_foldl_spmf_cons :
  fixes
    x :: 'a and
    xs :: "'a list"
  shows "
    prob_fail (foldl_spmf f p (x # xs))
    = prob_fail p + prob_fail (foldl_spmf f p xs)"
  sorry *)

lemma prob_fail_step : "
  prob_fail (step state x) \<le> 2 powr threshold"
  sorry

lemma prob_fail_estimate_size :
  fixes xs :: "'a list"
  defines "len \<equiv> length xs"
  shows "prob_fail (estimate_size xs) \<le> len * 2 powr threshold"
  sorry

end

end

end