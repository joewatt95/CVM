theory Utils_SPMF_Rel

imports
  CVM.Utils_SPMF_Common

begin

lemma prob_fail_eq_of_rel_spmf :
  assumes \<open>rel_spmf R p p'\<close>
  shows \<open>prob_fail p = prob_fail p'\<close>

  using assms
  by (simp add: pmf_None_eq_weight_spmf prob_fail_def rel_spmf_weightD)

definition equiv_up_to_failure ::
  \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a spmf \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'b spmf \<Rightarrow> bool\<close>
  (\<open>\<turnstile> \<lbrakk> _ \<rbrakk> _ \<simeq> \<lbrakk> _ \<rbrakk> _\<close>) where
  \<open>\<turnstile> \<lbrakk> P \<rbrakk> p \<simeq> \<lbrakk> P' \<rbrakk> p' \<equiv> rel_spmf (\<lambda> x x'. P x \<longleftrightarrow> P' x') p p'\<close>

lemma equiv_up_to_failure_refl_intro :
  assumes \<open>p = p'\<close>
  shows \<open>\<turnstile> \<lbrakk> P \<rbrakk> p \<simeq> \<lbrakk> P \<rbrakk> p'\<close>

  by (simp add: assms equiv_up_to_failure_def rel_spmf_reflI)

lemma equiv_up_to_failure_symm :
  assumes \<open>\<turnstile> \<lbrakk>P\<rbrakk>p \<simeq> \<lbrakk>P'\<rbrakk>p'\<close>
  shows \<open>\<turnstile> \<lbrakk>P'\<rbrakk>p' \<simeq> \<lbrakk>P\<rbrakk>p\<close>

  using assms
  by (metis (mono_tags, lifting) conversep_iff equiv_up_to_failure_def option.rel_conversep pmf.rel_flip rel_spmf_mono_strong) 

lemma prob_le_fail_of_equiv :
  fixes p p' P P'
  assumes \<open>\<turnstile> \<lbrakk>P\<rbrakk>p \<simeq> \<lbrakk>P'\<rbrakk>p'\<close>
  defines
    \<open>prob \<equiv> \<P>(x in measure_spmf p. P x)\<close> and
    \<open>prob' \<equiv> \<P>(x' in measure_spmf p'. P' x')\<close>
  shows
    \<open>prob \<le> prob' + prob_fail p\<close> and
    \<open>\<bar>prob - prob'\<bar> \<le> prob_fail p\<close>
proof -
  show \<open>prob \<le> prob' + prob_fail p\<close>
    by (smt (verit, best) Collect_cong UNIV_I assms(1) assms(3) ennreal_inj equiv_up_to_failure_def measure_le_0_iff measure_spmf.bounded_measure measure_spmf.emeasure_eq_measure mem_Collect_eq nn_integral_cong nn_integral_spmf prob_def prob_fail_def rel_spmf_measureD space_count_space space_measure_spmf weight_return_pmf_None weight_spmf_conv_pmf_None weight_spmf_le_1)

  then show \<open>\<bar>prob - prob'\<bar> \<le> prob_fail p\<close>
    using equiv_up_to_failure_symm
    by (smt (verit, best) Collect_cong UNIV_I assms(1) assms(3) ennreal_inj equiv_up_to_failure_def measure_nonneg measure_spmf.bounded_measure measure_spmf.emeasure_eq_measure mem_Collect_eq nn_integral_cong nn_integral_spmf prob_def rel_spmf_measureD space_count_space space_measure_spmf weight_return_pmf_None)
qed

end