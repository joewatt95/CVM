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

thm option.case_distrib [of pmf, symmetric]

lemma pmf_foldM_spmf_cons : "
  pmf (foldM_spmf f (x # xs) acc)
  = (\<lambda> b.
      \<integral> acc'.
        (case acc' of
          None \<Rightarrow> pmf fail_spmf b |
          Some acc' \<Rightarrow> pmf (foldM_spmf f xs acc') b)
        \<partial> f x acc)"
  apply simp
  unfolding bind_spmf_def pmf_bind
  apply (subst option.case_distrib [of pmf])
  sorry
  (* by (metis ext not_Some_eq option.simps(4) option.simps(5)) *)
  (* by (metis bind_spmf_def option.case_distrib pmf_bind)  *)

lemma prob_fail_foldM_spmf :
  fixes
    xs :: "'a list"
  assumes "\<And> x acc. prob_fail (f acc x) \<le> p"
  shows "prob_fail (foldM_spmf f xs acc) \<le> length xs * p"
proof (induction xs)
 case Nil then show ?case unfolding prob_fail_def by simp
next
  case (Cons x xs)
  then show ?case sorry
qed

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