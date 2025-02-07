theory Utils_PMF_Relational_Hoare

imports
  Utils_PMF_FoldM_Hoare

begin

lemma rel_pmf_bindI1 :
  assumes \<open>\<And> x. x \<in> set_pmf p \<Longrightarrow> rel_pmf R (f x) q\<close>
  shows \<open>rel_pmf R (p \<bind> f) q\<close>
  using assms rel_spmf_bindI1 rel_spmf_spmf_of_pmf
  by (metis bind_spmf_of_pmf lossless_spmf_spmf_of_spmf set_spmf_spmf_of_pmf spmf_of_pmf_bind)

lemma rel_pmf_bindI2 :
  assumes \<open>\<And> x. x \<in> set_pmf q \<Longrightarrow> rel_pmf R p (f x)\<close>
  shows \<open>rel_pmf R p (q \<bind> f)\<close>
  using assms rel_spmf_bindI2 rel_spmf_spmf_of_pmf
  by (metis bind_spmf_of_pmf lossless_spmf_spmf_of_spmf set_spmf_spmf_of_pmf spmf_of_pmf_bind)

abbreviation relational_hoare_triple
  (\<open>\<turnstile>pmf \<lbrakk> _ \<rbrakk> \<langle> _ | _ \<rangle> \<lbrakk> _ \<rbrakk>\<close> [21, 20, 20, 21] 60) where
  \<open>(\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>S\<rbrakk>) \<equiv> (\<And> x x'. R x x' \<Longrightarrow> rel_pmf S (f x) (f' x'))\<close>

lemma skip_left [simp] :
  \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f >>> return_pmf | f'\<rangle> \<lbrakk>S\<rbrakk> \<equiv> (\<And> x. \<turnstile>pmf \<lbrakk>R x\<rbrakk> f' \<lbrakk>S (f x)\<rbrakk>)\<close>
  by (simp add: AE_measure_pmf_iff rel_pmf_return_pmf1)

lemma skip_right [simp] :
  \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f' >>> return_pmf\<rangle> \<lbrakk>S\<rbrakk> \<equiv>
    (\<And> x'. \<turnstile>pmf \<lbrakk>flip R x'\<rbrakk> f \<lbrakk>flip S (f' x')\<rbrakk>)\<close>
  apply standard
  by (simp_all add: AE_measure_pmf_iff rel_pmf_return_pmf2)

context
  fixes
    R :: \<open>nat \<Rightarrow> 'b \<Rightarrow>'c \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

private abbreviation (input)
  \<open>foldM_enumerate' \<equiv> \<lambda> f. foldM_pmf_enumerate f xs offset\<close>

private abbreviation (input)
  \<open>R' \<equiv> \<lambda> idx x val val'.
    (idx, x) \<in> set (List.enumerate offset xs) \<and>
    R idx val val'\<close>

lemma loop_enumerate :
  assumes \<open>\<And> index x.
    \<turnstile>pmf \<lbrakk>R' index x\<rbrakk> \<langle>f (index, x) | f' (index, x)\<rangle> \<lbrakk>R (Suc index)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf
    \<lbrakk>R offset\<rbrakk>
    \<langle>foldM_enumerate' f | foldM_enumerate' f'\<rangle>
    \<lbrakk>R (offset + length xs)\<rbrakk>\<close>
using assms proof (induction xs arbitrary: offset)
  case Nil
  then show ?case by (simp add: foldM_enumerate_def)
next
  case (Cons _ _)
  then show ?case
    apply (simp flip: add_Suc add: foldM_enumerate_def)
    by (blast intro: rel_pmf_bindI)
qed

lemma loop :
  assumes \<open>\<And> idx x.
    \<turnstile>pmf \<lbrakk>R' idx x\<rbrakk> \<langle>f x | f' x\<rangle> \<lbrakk>R (Suc idx)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf
    \<lbrakk>R offset\<rbrakk>
    \<langle>foldM_pmf f xs | foldM_pmf f' xs\<rangle>
    \<lbrakk>R (offset + length xs)\<rbrakk>\<close>
  using assms loop_enumerate
  by (metis foldM_eq_foldM_enumerate prod.sel(2))

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f x | f' x\<rangle> \<lbrakk>R\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>foldM_pmf f xs | foldM_pmf f' xs\<rangle> \<lbrakk>R\<rbrakk>\<close>
  using assms loop[where offset = 0 and R = \<open>\<lblot>R\<rblot>\<close>] by blast

end