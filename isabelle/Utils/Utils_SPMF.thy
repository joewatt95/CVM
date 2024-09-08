theory Utils_SPMF

imports
  "HOL-Probability.SPMF"
  "HOL-Probability.Hoeffding"
  CVM.Utils_Function

begin

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

lemma integrable_prob_fail_foldM_spmf :
  \<open>integrable
    (measure_spmf <| f x acc) <|
    prob_fail <<< (foldM_spmf f xs)\<close>

  by (auto
      intro!: measure_spmf.integrable_const_bound[where ?B = 1]
      simp add: prob_fail_def pmf_le_1)

lemma prob_fail_foldM_spmf :
  fixes
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

    then show ?thesis
      using local.Cons assms foldM_spmf.integrable_prob_fail_foldM_spmf
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

(* lemma prob_loop :
  fixes
    P :: \<open>'b \<Rightarrow> bool\<close>
  assumes
    \<open>P acc\<close> and
    (* x \<in> set_spmf (f x acc) \<bind> set_spmf \<circ> foldM_spmf f xs *)
    \<open>\<And> x acc.
      (\<exists> acc' \<in> set_spmf (f x acc). acc \<in> set_spmf (foldM_spmf f xs acc'))
      \<Longrightarrow> P acc\<close>
  shows \<open>AE acc' in measure_spmf (foldM_spmf f xs acc). P acc'\<close>
proof (induction xs)
  case Nil
  then show ?case using assms by auto
next
  case (Cons x xs)
  show ?case
    apply (auto simp add: set_bind_spmf)
    (* apply (subst (asm) set_bind_spmf) *)
    sorry
qed *)

lemma prob_loop :
  fixes
    P :: \<open>'b \<Rightarrow> bool\<close> and
    p :: real
  assumes
    \<open>P acc \<and> (case xs of
      [] \<Rightarrow> True |
      x # xs \<Rightarrow>
        \<forall> acc'' \<in> set_spmf (f x acc).
          P acc'' \<and> acc' \<in> set_spmf (foldM_spmf f xs acc''))\<close>
  shows \<open>AE acc' in measure_spmf (foldM_spmf f xs acc). P acc'\<close>
proof (induction xs)
 case Nil
  then show ?case using assms by auto
next
  case (Cons x xs)

  then show ?case
  proof (cases xs)
    case Nil
    then show ?thesis
      using assms
      apply auto
      sorry
  next
    case (Cons a list)
    then show ?thesis sorry
  qed
qed

end

end