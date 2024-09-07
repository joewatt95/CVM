theory Basic_Props

imports
  HOL.Power
  "HOL-Probability.Product_PMF"
  "HOL-Probability.Hoeffding"
  CVM.Basic_Algo
  CVM.Utils_Approx_Algo
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

lemma pmf_foldM_spmf_cons :
  \<open>pmf (foldM_spmf f (x # xs) acc) a
  = \<integral> acc'. (
      case acc' of
        None \<Rightarrow> pmf fail_spmf a |
        Some acc' \<Rightarrow> pmf (foldM_spmf f xs acc') a)
      \<partial> f x acc\<close>

  apply (simp add: bind_spmf_def pmf_bind)
  by (metis (mono_tags, lifting) option.exhaust option.simps(4) option.simps(5))

(* find_theorems \<open>integrable (measure_spmf _)\<close>

thm measure_spmf.integrable_const_bound *)

lemma prob_fail_foldM_spmf :
  fixes
    f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close> and
    x :: 'a and
    xs :: \<open>'a list\<close> and
    acc :: 'b and
    p :: real
  assumes
    \<open>p \<ge> 0\<close> and
    \<open>\<And> x acc. prob_fail (f x acc) \<le> p\<close>
  shows \<open>prob_fail (foldM_spmf f xs acc) \<le> length xs * p\<close>
proof (induction xs arbitrary: acc)
 case Nil
 then show ?case unfolding prob_fail_def by simp
next
  case (Cons x xs)

  then have
    \<open>prob_fail (foldM_spmf f (x # xs) acc)
      = prob_fail (f x acc)
      + \<integral> acc'. prob_fail (foldM_spmf f xs acc') \<partial> measure_spmf (f x acc)\<close>
    by (simp add: prob_fail_def pmf_bind_spmf_None)

  also have
    \<open>... \<le> p + \<integral> acc'. length xs * p \<partial> measure_spmf (f x acc)\<close>
  proof -
    have * : \<open>\<And> a a' b b' :: real. \<lbrakk>a \<le> a'; b \<le> b'\<rbrakk> \<Longrightarrow> a + b \<le> a' + b'\<close>
      by simp

    then show ?thesis
      using local.Cons assms integrable_prob_fail_foldM_spmf
      apply (intro *)
      apply blast
      apply (intro integral_mono)
      by simp_all
  qed

  also have \<open>... \<le> p + length xs * p\<close>
  proof -
    have * : \<open>\<And> a b c :: real.
      \<lbrakk>a \<in> {0 .. 1}; b \<ge> 0; c \<ge> 0\<rbrakk> \<Longrightarrow> a * (b * c) \<le> b * c\<close>
      by (simp add: mult_left_le_one_le mult_mono)

    show ?thesis using assms by (auto intro!: * simp add: weight_spmf_le_1)
  qed

  finally show ?case by (simp add: distrib_right)
qed

lemma prob_fail_step :
  \<open>prob_fail (step state x) \<le> 2 powr threshold\<close>
  sorry

lemma prob_fail_estimate_size :
  fixes xs :: \<open>'a list\<close>
  shows \<open>prob_fail (estimate_size xs) \<le> length xs * 2 powr threshold\<close>
proof -
  have
    \<open>prob_fail (estimate_size xs) = prob_fail (run_steps initial_state xs)\<close>
    by (simp add: estimate_size_def prob_fail_def pmf_None_eq_weight_spmf)

  then show ?thesis
    by (auto
        intro!: prob_fail_foldM_spmf prob_fail_step
        simp add: run_steps_def)
qed

end

end

end