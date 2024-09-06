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

(* thm option.case_distrib [of pmf, symmetric] *)

(* lemma pmf_foldM_spmf_cons : "
  pmf (foldM_spmf f (x # xs) acc) a
  = \<integral> acc'. (
      case acc' of
        None \<Rightarrow> pmf fail_spmf a |
        Some acc' \<Rightarrow> pmf (foldM_spmf f xs acc') a)
      \<partial> f x acc"
  apply simp
  unfolding bind_spmf_def pmf_bind
  apply (subst option.case_distrib [of pmf])
  sorry *)

(* lemma spmf_foldM_spmf_cons :
  assumes "
    integrable
      (measure_spmf (f x acc))
      (\<lambda> acc'. spmf (foldM_spmf f xs acc') acc'')"
  shows "
    spmf (foldM_spmf f (x # xs) acc) acc''
    = \<integral> acc'.
        spmf (f x acc) acc' * spmf (foldM_spmf f xs acc') acc''
        \<partial> count_space UNIV"
  by (simp add: assms integral_measure_spmf spmf_bind) *)

find_theorems "integrable (measure_pmf _)"

lemma prob_fail_foldM_spmf :
  fixes
    p :: real and
    xs :: "'a list"
  assumes "
    p \<ge> 0" and "
    \<And> x acc. prob_fail (f x acc) \<le> p" and "
    integrable
      (measure_spmf <| f x acc) <|
      prob_fail \<circ> (foldM_spmf f xs)"
  shows "prob_fail (foldM_spmf f xs acc) \<le> length xs * p"
proof (induction xs arbitrary: acc)
 case Nil then show ?case unfolding prob_fail_def by simp
next
  case (Cons x xs)

  then have ih : "\<And> acc. prob_fail (foldM_spmf f xs acc) \<le> length xs * p"
    by blast

  then have "
    prob_fail (foldM_spmf f (x # xs) acc)
    = prob_fail (f x acc)
      + \<integral> acc'. prob_fail (foldM_spmf f xs acc') \<partial> measure_spmf (f x acc)"
    unfolding prob_fail_def by (simp add: pmf_bind_spmf_None)

  also have "
    ... \<le> p + \<integral> acc'. length xs * p \<partial> measure_spmf (f x acc)"
  proof -
    have * : "\<And> a a' b b' :: real.
      \<lbrakk>a \<le> a'; b \<le> b'\<rbrakk> \<Longrightarrow> a + b \<le> a' + b'"
      by simp

    then show ?thesis
      using assms apply (subst *, blast)
      apply (rule integral_mono)
      apply simp_all
      sorry
  qed

  (* also have "
    ... = p + (length xs * p) * \<integral> acc'. 1 \<partial> measure_spmf (f x acc)"
    by simp *)

  also have "
    ... \<le> p + (length xs * p) * 1"
  proof -
    have * : "\<And> a b c :: real.
      \<lbrakk>a \<in> {0 .. 1}; b \<ge> 0; c \<ge> 0\<rbrakk> \<Longrightarrow> a * b * c \<le> b * c"
      by (simp add: mult_left_le_one_le mult_mono)

    show ?thesis
      apply simp
      apply (rule *)
      using assms by (auto simp add: weight_spmf_le_1)
  qed

  finally show ?case
    using assms
    apply simp
    sorry
qed

lemma prob_fail_step : "
  prob_fail (step state x) \<le> 2 powr threshold"
  sorry

lemma prob_fail_estimate_size :
  fixes xs :: "'a list"
  shows "prob_fail (estimate_size xs) \<le> length xs * 2 powr threshold"
proof -
  have [simp] : "
    prob_fail (estimate_size xs) = prob_fail (run_steps initial_state xs)"
    apply (simp add: estimate_size_def)
    sorry

  then show ?thesis
    apply (simp add: run_steps_def)
    apply (rule prob_fail_foldM_spmf)
    apply (auto intro: prob_fail_step)
    sorry
qed

end

end

end