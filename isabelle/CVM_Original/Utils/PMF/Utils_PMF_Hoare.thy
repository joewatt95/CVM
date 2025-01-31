theory Utils_PMF_Hoare

imports
  Utils_PMF_Basic

begin

abbreviation hoare_triple
  (\<open>\<turnstile>pmf \<lbrakk> _ \<rbrakk> _ \<lbrakk> _ \<rbrakk> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<equiv> (\<And> x. P x \<Longrightarrow> AE y in measure_pmf <| f x. Q y)\<close>

lemma skip [simp] :
  \<open>(\<turnstile>pmf \<lbrakk>P\<rbrakk> return_pmf \<lbrakk>Q\<rbrakk>) \<equiv> (\<And> x. P x \<Longrightarrow> Q x)\<close>
  \<open>(\<turnstile>pmf \<lbrakk>P\<rbrakk> (\<lambda> x. return_pmf (f x)) \<lbrakk>Q\<rbrakk>) \<equiv> (\<And> x. P x \<Longrightarrow> Q (f x))\<close>
  by (simp_all add: AE_measure_pmf_iff)

(* lemma seq :
  assumes
    \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<close>
    \<open>\<turnstile>pmf \<lbrakk>Q\<rbrakk> g \<lbrakk>R\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> (\<lambda> x. f x \<bind> g) \<lbrakk>R\<rbrakk>\<close>
  using assms by (auto iff: AE_measure_pmf_iff simp add: hoare_triple_def)

lemma seq' :
  assumes
    \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
    \<open>\<And> x. P x \<Longrightarrow> \<turnstile>pmf \<lbrakk>Q\<rbrakk> g x \<lbrakk>R\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> (\<lambda> x. f x \<bind> g x) \<lbrakk>R\<rbrakk>\<close>
  using assms by (smt (verit, ccfv_threshold) hoare_triple_def seq) *)

context
  fixes
    P :: \<open>nat \<Rightarrow> 'b \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

private abbreviation (input)
  \<open>P' \<equiv> \<lambda> idx x val.
    (idx, x) \<in> set (List.enumerate offset xs) \<and>
    P idx val\<close>

lemma loop_enumerate :
  assumes \<open>\<And> idx x. \<turnstile>pmf \<lbrakk>P' idx x\<rbrakk> f (idx, x) \<lbrakk>P (Suc idx)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf
    \<lbrakk>P offset\<rbrakk>
    foldM_pmf_enumerate f xs offset
    \<lbrakk>P (offset + length xs)\<rbrakk>\<close>
using assms proof (induction xs arbitrary: offset)
  case Nil
  then show ?case by (simp add: AE_measure_pmf_iff foldM_enumerate_def)
next
  case (Cons _ _)
  then show ?case
    apply (simp add: AE_measure_pmf_iff foldM_enumerate_def)
    by (metis add_Suc_right add_Suc_shift)
qed

lemma loop :
  assumes \<open>\<And> idx x. \<turnstile>pmf \<lbrakk>P' idx x\<rbrakk> f x \<lbrakk>P (Suc idx)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P offset\<rbrakk> foldM_pmf f xs \<lbrakk>P (offset + length xs)\<rbrakk>\<close>
  using assms loop_enumerate
  by (metis foldM_eq_foldM_enumerate prod.sel(2))

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile>pmf \<lbrakk>P\<rbrakk> f x \<lbrakk>P\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> foldM_pmf f xs \<lbrakk>P\<rbrakk>\<close>
  using assms loop[where offset = 0 and P = \<open>\<lblot>P\<rblot>\<close>] by blast

end
