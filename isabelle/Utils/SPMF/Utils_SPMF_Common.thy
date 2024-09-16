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
  shows
    \<open>prob_fail p = prob_fail p'\<close> and
    \<open>\<bar>prob - prob'\<bar> \<le> prob_fail p\<close> and
    \<open>prob \<le> prob' + prob_fail p\<close>
proof -
  show \<open>prob_fail p = prob_fail p'\<close>
    by (metis assms(1) equiv_up_to_failure_def pmf_None_eq_weight_spmf prob_fail_def rel_spmf_weightD)
  
  then show \<open>\<bar>prob - prob'\<bar> \<le> prob_fail p\<close>
    using assms
    apply (auto simp add: equiv_up_to_failure_def prob_fail_def measure_measure_spmf_conv_measure_pmf)
    sorry

  then show \<open>prob \<le> prob' + prob_fail p\<close> by linarith

qed


end