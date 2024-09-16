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

definition equiv_up_to_failure ::
  \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a spmf \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'b spmf \<Rightarrow> bool\<close>
  (\<open>\<turnstile> \<lbrakk> _ \<rbrakk> _ \<simeq> \<lbrakk> _ \<rbrakk> _\<close>) where
  \<open>\<turnstile> \<lbrakk> P \<rbrakk> p \<simeq> \<lbrakk> P' \<rbrakk> p' \<equiv> rel_spmf (\<lambda> x x'. P x \<longleftrightarrow> P' x') p p'\<close>

lemma test :
  fixes p p' P P'
  assumes \<open>\<turnstile> \<lbrakk>P\<rbrakk>p \<simeq> \<lbrakk>P'\<rbrakk>p'\<close>
  defines
    \<open>prob \<equiv> \<P>(x in measure_spmf p. P x)\<close> and
    \<open>prob' \<equiv> \<P>(x' in measure_spmf p'. P' x')\<close>
  shows \<open>prob \<le> prob' + prob_fail p\<close>

  by (smt (verit, best) Collect_cong UNIV_I assms(1) assms(3) ennreal_inj equiv_up_to_failure_def measure_le_0_iff measure_spmf.bounded_measure measure_spmf.emeasure_eq_measure mem_Collect_eq nn_integral_cong nn_integral_spmf prob_def prob_fail_def rel_spmf_measureD space_count_space space_measure_spmf weight_return_pmf_None weight_spmf_conv_pmf_None weight_spmf_le_1)

end