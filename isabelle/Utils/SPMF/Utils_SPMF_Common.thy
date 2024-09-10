theory Utils_SPMF_Common

imports
  "HOL-Probability.SPMF"
  CVM.Utils_Function

begin

abbreviation fail_spmf :: \<open>'a spmf\<close> where
  \<open>fail_spmf \<equiv> return_pmf None\<close>

definition prob_fail :: \<open>'a spmf \<Rightarrow> real\<close> where
  \<open>prob_fail \<equiv> flip pmf None\<close>

definition kleisli_compose_left ::
  \<open>('a \<Rightarrow> 'b spmf) \<Rightarrow> ('b \<Rightarrow> 'c spmf) \<Rightarrow> 'a \<Rightarrow> 'c spmf\<close>
  (infixl \<open>>=>\<close> 50) where
  \<open>(f >=> g) \<equiv> \<lambda> x. bind_spmf (f x) g\<close>

definition kleisli_compose_right (infixr \<open><=<\<close> 50) where
  \<open>(f <=< g) \<equiv> g >=> f\<close>

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

lemma integrable_prob_fail_foldM_spmf :
  \<open>integrable
    (measure_spmf <| f x acc) <|
    prob_fail <<< (foldM_spmf f xs)\<close>

  by (auto
      intro!: measure_spmf.integrable_const_bound[where ?B = 1]
      simp add: prob_fail_def pmf_le_1)

end

end