subsection \<open>foldM\_pmf and related Hoare rules\<close>

theory Utils_PMF_FoldM_Hoare

imports
  Utils_PMF_Basic

begin

subsubsection \<open>foldM\_pmf\<close>

abbreviation \<open>foldM_pmf \<equiv> foldM bind_pmf return_pmf\<close>
abbreviation \<open>foldM_pmf_enumerate \<equiv> foldM_enumerate bind_pmf return_pmf\<close>

lemma foldM_pmf_snoc :
  "foldM_pmf f (xs @ [x]) val = bind_pmf (foldM_pmf f xs val) (f x)"
  apply (induction xs arbitrary:val)
    by (simp_all
      add: bind_return_pmf bind_return_pmf' bind_assoc_pmf
      cong: bind_pmf_cong)

subsubsection \<open>Hoare triple for Kleisli morphisms over PMF\<close>

abbreviation pmf_hoare_triple
  (\<open>\<turnstile>pmf \<lbrakk> _ \<rbrakk> _ \<lbrakk> _ \<rbrakk> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<equiv> (\<And> x. P x \<Longrightarrow> AE y in measure_pmf <| f x. Q y)\<close>

subsubsection \<open>Hoare rules for foldM\_pmf\<close>

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

lemma pmf_hoare_foldM_enumerate :
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

lemma pmf_hoare_foldM_indexed' :
  assumes \<open>\<And> idx x. \<turnstile>pmf \<lbrakk>P' idx x\<rbrakk> f x \<lbrakk>P (Suc idx)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P offset\<rbrakk> foldM_pmf f xs \<lbrakk>P (offset + length xs)\<rbrakk>\<close>
  using assms pmf_hoare_foldM_enumerate
  by (metis foldM_eq_foldM_enumerate prod.sel(2))

end

lemmas pmf_hoare_foldM_indexed =
  pmf_hoare_foldM_indexed'[where offset = 0, simplified]

lemma pmf_hoare_foldM :
  assumes \<open>\<And> x. \<turnstile>pmf \<lbrakk>P\<rbrakk> f x \<lbrakk>P\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> foldM_pmf f xs \<lbrakk>P\<rbrakk>\<close>
  using assms pmf_hoare_foldM_indexed[where P = \<open>\<lblot>P\<rblot>\<close>] by blast

end
