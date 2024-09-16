theory Utils_SPMF_Common

imports
  "HOL-Probability.SPMF"
  CVM.Utils_Function

begin

definition fail_spmf :: \<open>'a spmf\<close> where
  \<open>fail_spmf \<equiv> return_pmf None\<close>

definition prob_fail :: \<open>'a spmf \<Rightarrow> real\<close> where
  \<open>prob_fail \<equiv> flip pmf None\<close>

definition kleisli_compose_left ::
  \<open>('a \<Rightarrow> 'b spmf) \<Rightarrow> ('b \<Rightarrow> 'c spmf) \<Rightarrow> 'a \<Rightarrow> 'c spmf\<close>
  (infixl \<open>>=>\<close> 50) where
  \<open>(f >=> g) \<equiv> \<lambda> x. bind_spmf (f x) g\<close>

definition kleisli_compose_right ::
  \<open>('b \<Rightarrow> 'c spmf) \<Rightarrow> ('a \<Rightarrow> 'b spmf) \<Rightarrow> 'a \<Rightarrow> 'c spmf\<close>
  (infixr \<open><=<\<close> 50) where
  \<open>(f <=< g) \<equiv> g >=> f\<close>

definition equiv_up_to_failure where
  \<open>equiv_up_to_failure P p P' p' \<equiv>
    rel_spmf (\<lambda> x x'. P x \<longleftrightarrow> P' x') p p'\<close>

lemma test :
  fixes p p' P P'
  assumes \<open>equiv_up_to_failure P p P' p'\<close>
  shows
    \<open>prob_fail p = prob_fail p'\<close> and
    \<open>\<bar>\<P>(x in measure_spmf p. P x) - \<P>(x' in measure_spmf p'. P' x')\<bar> \<le> prob_fail p\<close>

  sorry

end