theory Utils_PMF

imports
  "HOL-Probability.Probability_Mass_Function"
  CVM_Subsample.Utils_Basic

begin

abbreviation foldM_pmf ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b pmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b pmf\<close> where
  \<open>foldM_pmf \<equiv> foldM bind_pmf return_pmf\<close>

lemma foldM_pmf_snoc: "foldM_pmf f (xs@[y]) val = bind_pmf (foldM_pmf f xs val) (f y)"
  by (induction xs arbitrary:val)
    (simp_all add: bind_return_pmf bind_return_pmf' bind_assoc_pmf cong:bind_pmf_cong)

abbreviation
  \<open>foldM_pmf_enumerate \<equiv> foldM_enumerate bind_pmf return_pmf\<close>

abbreviation (input) possibly_evals_to
  (\<open>\<turnstile>pmf _ \<Rightarrow>? _\<close> [20, 2] 60) where
  \<open>\<turnstile>pmf p \<Rightarrow>? x \<equiv> x \<in> set_pmf p\<close>

abbreviation (input) hoare_triple ::
  \<open>('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b pmf) \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> prop\<close>
  (\<open>\<turnstile>pmf \<lbrakk> _ \<rbrakk> _ \<lbrakk> _ \<rbrakk> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<equiv> (\<And> x y. \<lbrakk>P x; \<turnstile>pmf f x \<Rightarrow>? y\<rbrakk> \<Longrightarrow> Q y)\<close>

(* lemma hoare_tripleI :
  assumes \<open>\<And> x y. \<lbrakk>P x; \<turnstile>pmf f x \<Rightarrow>? y\<rbrakk> \<Longrightarrow> Q y\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  by (metis assms)

lemma hoare_tripleE :
  assumes
    \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
    \<open>P x\<close>
    \<open>\<turnstile>pmf f x \<Rightarrow>? y\<close>
  shows \<open>Q y\<close>
  by (metis assms)

lemma precond_strengthen :
  assumes
    \<open>\<And> x. P x \<Longrightarrow> P' x\<close>
    \<open>\<turnstile>pmf \<lbrakk>P'\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  by (metis assms(1,2)) 

lemma precond_false [simp] :
  \<open>\<turnstile>pmf \<lbrakk>\<lblot>False\<rblot>\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  by (simp add: hoare_tripleI) *)

lemma skip [simp] :
  \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> return_pmf \<lbrakk>Q\<rbrakk> \<equiv> (\<And> x. P x \<Longrightarrow> Q x)\<close>
  \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> (\<lambda> x. return_pmf (f x)) \<lbrakk>Q\<rbrakk> \<equiv> (\<And> x. P x \<Longrightarrow> Q (f x))\<close>
  by simp_atomize+

lemma if_then_else :
  assumes
    \<open>\<And> x. f x \<Longrightarrow> \<turnstile>pmf \<lbrakk>(\<lambda> x'. x = x' \<and> P x)\<rbrakk> g \<lbrakk>Q\<rbrakk>\<close>
    \<open>\<And> x. \<not> f x \<Longrightarrow> \<turnstile>pmf \<lbrakk>(\<lambda> x'. x = x' \<and> P x)\<rbrakk> h \<lbrakk>Q\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> (\<lambda> x. if f x then g x else h x) \<lbrakk>Q\<rbrakk>\<close>
  using assms by (simp split: if_splits)

(* lemma seq :
  assumes
    \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
    \<open>\<turnstile>pmf \<lbrakk>Q\<rbrakk> g \<lbrakk>R\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> (\<lambda> x. f x \<bind> g) \<lbrakk>R\<rbrakk>\<close>
  using assms by auto *)

lemma seq :
  assumes
    \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
    \<open>\<And> x. P x \<Longrightarrow> \<turnstile>pmf \<lbrakk>Q\<rbrakk> g x \<lbrakk>R\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> (\<lambda> x. f x \<bind> g x) \<lbrakk>R\<rbrakk>\<close>
  using assms by simp' 

context
  fixes
    P :: \<open>nat \<Rightarrow> 'b \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

private abbreviation (input)
  \<open>P' index x val \<equiv> (
    (index, x) \<in> set (List.enumerate offset xs) \<and>
    P index val)\<close>

lemma loop_enumerate :
  assumes \<open>\<And> index x. \<turnstile>pmf \<lbrakk>P' index x\<rbrakk> f (index, x) \<lbrakk>P (Suc index)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf
    \<lbrakk>P offset\<rbrakk>
    foldM_pmf_enumerate f xs offset
    \<lbrakk>P (offset + length xs)\<rbrakk>\<close>
using assms proof (induction xs arbitrary: offset)
  case Nil
  then show ?case by (simp add: foldM_enumerate_def)
next
  case (Cons _ _)
  then show ?case
    apply (simp add: foldM_enumerate_def)
    by (metis add_Suc)
qed

lemma loop :
  assumes \<open>\<And> index x. \<turnstile>pmf \<lbrakk>P' index x\<rbrakk> f x \<lbrakk>P (Suc index)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P offset\<rbrakk> foldM_pmf f xs \<lbrakk>P (offset + length xs)\<rbrakk>\<close>
  using assms loop_enumerate foldM_eq_foldM_enumerate
  by (metis comp_apply snd_conv)

end

lemma loop' :
  assumes \<open>\<And> x. \<turnstile>pmf \<lbrakk>P\<rbrakk> f x \<lbrakk>P\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> foldM_pmf f xs \<lbrakk>P\<rbrakk>\<close>
  using loop[where ?P = \<open>curry <| snd >>> P\<close>] assms by simp'

end