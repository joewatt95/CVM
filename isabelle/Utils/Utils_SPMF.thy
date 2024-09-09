theory Utils_SPMF

imports
  "HOL-Probability.SPMF"
  "HOL-Probability.Hoeffding"
  CVM.Utils_Function

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

abbreviation fail_spmf :: \<open>'a spmf\<close> where
  \<open>fail_spmf \<equiv> return_pmf None\<close>

definition prob_fail :: \<open>'a spmf \<Rightarrow> real\<close> where
  \<open>prob_fail \<equiv> flip pmf None\<close>

fun
  foldM_spmf :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b spmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close> where
  \<open>foldM_spmf _ [] acc = return_spmf acc\<close> |
  \<open>foldM_spmf f (x # xs) acc = f x acc \<bind> foldM_spmf f xs\<close>

locale foldM_spmf =
  fixes
    f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close> and
    x :: 'a and
    xs :: \<open>'a list\<close> and
    acc :: 'b
begin

lemma pmf_foldM_spmf_nil :
  fixes acc' :: 'b
  shows
    \<open>spmf (foldM_spmf f [] acc) acc = 1\<close> and
    \<open>acc \<noteq> acc' \<Longrightarrow> spmf (foldM_spmf f [] acc) acc' = 0\<close>
  by auto

lemma pmf_foldM_spmf_cons :
  \<open>pmf (foldM_spmf f (x # xs) acc) a
  = \<integral> acc'. (
      case acc' of
        None \<Rightarrow> pmf fail_spmf a |
        Some acc' \<Rightarrow> pmf (foldM_spmf f xs acc') a)
      \<partial> f x acc\<close>

  apply (simp add: bind_spmf_def pmf_bind)
  by (metis (mono_tags, lifting) option.exhaust option.simps(4) option.simps(5))

(* find_theorems \<open>integrable (measure_spmf _)\<close> *)

(* thm measure_spmf.integrable_const_bound *)

lemma loop :
  fixes P :: \<open>'b \<Rightarrow> bool\<close>
  assumes \<open>\<And> x acc. P acc \<Longrightarrow> AE acc' in measure_spmf (f x acc). P acc'\<close>
  shows \<open>\<And> acc. P acc \<Longrightarrow> AE acc' in measure_spmf (foldM_spmf f xs acc). P acc'\<close>
proof (induction xs)
  case Nil
  then show ?case using assms by simp
next
  case (Cons x xs)

  {
    fix acc acc'
    assume
      \<open>P acc\<close> and
      \<open>acc' \<in> set_spmf (f x acc \<bind> foldM_spmf f xs)\<close>

    then obtain acc'' where
      \<open>acc'' \<in> set_spmf (f x acc)\<close> and
      \<open>acc' \<in> set_spmf (foldM_spmf f xs acc'')\<close>
      by (auto simp add: set_bind_spmf)

    then have \<open>P acc'\<close> by (metis AE_measure_spmf_iff assms Cons.IH \<open>P acc\<close>)
  }

  then show ?case using Cons.prems by simp
qed

(* find_theorems "_ = measure _ _ * measure _ _"  *)

(* lemma loop' :
  fixes
    P :: \<open>'b \<Rightarrow> bool\<close> and
    p :: real
  assumes
    \<open>\<And> x acc. P acc \<Longrightarrow> \<P>(acc' in measure_spmf (f x acc). P acc') = p\<close>
  shows
    \<open>\<And> acc.
      P acc
      \<Longrightarrow> \<P>(acc' in measure_spmf (foldM_spmf f xs acc). P acc')
          = p ^ length xs\<close>
proof (induction xs)
  case Nil
  then show ?case
    using assms by (simp add: measure_return measure_spmf_return_spmf)
next
  case (Cons x xs)

  then have
    \<open>\<P>(acc' in measure_spmf (f x acc). P acc') = p\<close> and
    \<open>\<P>(acc' in measure_spmf (foldM_spmf f xs acc). P acc') = p ^ length xs\<close>
    using assms
    apply blast
    by (simp add: Cons.IH Cons.prems)

  moreover have
    \<open>\<P>(acc' in measure_spmf (foldM_spmf f (x # xs) acc). P acc')
      = \<P>(acc' in measure_spmf (f x acc). P acc')
        * \<P>(acc' in measure_spmf (foldM_spmf f xs acc). P acc')\<close>
    apply (simp add: measure_spmf_bind)
    sorry

  then show ?case using assms local.Cons.IH Cons.prems by simp
qed *)

lemma integrable_prob_fail_foldM_spmf :
  \<open>integrable
    (measure_spmf <| f x acc) <|
    prob_fail <<< (foldM_spmf f xs)\<close>

  by (auto
      intro!: measure_spmf.integrable_const_bound[where ?B = 1]
      simp add: prob_fail_def pmf_le_1)

lemma prob_fail_foldM_spmf_le :
  fixes
    p :: real and
    P :: \<open>'b \<Rightarrow> bool\<close>
  assumes
    \<open>p \<ge> 0\<close> and
    \<open>\<And> x acc.
      P acc
      \<Longrightarrow> prob_fail (f x acc) \<le> p
          \<and> (AE acc' in measure_spmf (f x acc). P acc')\<close>
  shows \<open>P acc \<Longrightarrow> prob_fail (foldM_spmf f xs acc) \<le> length xs * p\<close>
proof (induction xs arbitrary: acc)
 case Nil
 then show ?case by (simp add: prob_fail_def)
next
  case (Cons x xs)

  let ?acc' = \<open>f x acc\<close>
  let ?\<mu>' = \<open>measure_spmf ?acc'\<close>

  have
    \<open>prob_fail (foldM_spmf f (x # xs) acc)
    = prob_fail ?acc' + \<integral> acc'. prob_fail (foldM_spmf f xs acc') \<partial> ?\<mu>'\<close>
    by (simp add: prob_fail_def pmf_bind_spmf_None)

  also have \<open>... \<le> p + \<integral> acc'. length xs * p \<partial> ?\<mu>'\<close>
  proof -
    have * : \<open>\<And> a a' b b' :: real. \<lbrakk>a \<le> a'; b \<le> b'\<rbrakk> \<Longrightarrow> a + b \<le> a' + b'\<close>
      by simp

    have \<open>AE acc' in measure_spmf (foldM_spmf f (x # xs) acc). P acc'\<close>
      by (meson \<open>P acc\<close> assms(2) foldM_spmf.loop)

    then have \<open>prob_fail ?acc' \<le> p\<close>
      using \<open>P acc\<close> assms(2) by blast

    moreover have
      \<open>AE acc' in ?\<mu>'. prob_fail (foldM_spmf f xs acc') \<le> length xs * p\<close>
      using assms Cons.IH \<open>P acc\<close> by simp

    moreover have
      \<open>(\<integral> acc'. prob_fail (foldM_spmf f xs acc') \<partial> ?\<mu>') \<le> \<integral> acc'. length xs * p \<partial> ?\<mu>'\<close>
      using assms(1) calculation(2) integral_mono_AE' by fastforce 

    ultimately show ?thesis
      using foldM_spmf.integrable_prob_fail_foldM_spmf
      by auto
  qed

  also have \<open>... \<le> p + length xs * p\<close>
  proof -
    have * : \<open>\<And> a b c :: real.
      \<lbrakk>a \<in> {0 .. 1}; b \<ge> 0; c \<ge> 0\<rbrakk> \<Longrightarrow> a * (b * c) \<le> b * c\<close>
      by (simp add: mult_left_le_one_le mult_mono)

    show ?thesis using assms by (auto intro!: * simp add: weight_spmf_le_1)
  qed

  finally show ?case by (simp add: distrib_left mult.commute) 
qed

end

end