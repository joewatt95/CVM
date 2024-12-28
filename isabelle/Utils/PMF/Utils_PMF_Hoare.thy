theory Utils_PMF_Hoare

imports
  CVM.Utils_PMF_Basic

begin

abbreviation possibly_evals_to
  (\<open>\<turnstile>pmf _ \<Rightarrow>? _\<close> [20, 2] 60) where
  \<open>\<turnstile>pmf p \<Rightarrow>? x \<equiv> x \<in> set_pmf p\<close>

lemma bind_pmfE :
  assumes \<open>\<turnstile>pmf f x \<bind> g \<Rightarrow>? z\<close>
  obtains y where
    \<open>\<turnstile>pmf f x \<Rightarrow>? y\<close>
    \<open>\<turnstile>pmf g y \<Rightarrow>? z\<close>
  using assms by auto

definition hoare_triple ::
  \<open>['a \<Rightarrow> bool, 'a \<Rightarrow> 'b pmf, 'b \<Rightarrow> bool] \<Rightarrow> bool\<close>
  (\<open>\<turnstile>pmf \<lbrakk> _ \<rbrakk> _ \<lbrakk> _ \<rbrakk> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<equiv> \<forall> x y. P x \<longrightarrow> (\<turnstile>pmf f x \<Rightarrow>? y) \<longrightarrow> Q y\<close>

lemma hoare_tripleI :
  assumes \<open>\<And> x y. \<lbrakk>P x; \<turnstile>pmf f x \<Rightarrow>? y\<rbrakk> \<Longrightarrow> Q y\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  by (metis assms hoare_triple_def)

lemma hoare_tripleE :
  assumes
    \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
    \<open>P x\<close>
    \<open>\<turnstile>pmf f x \<Rightarrow>? y\<close>
  shows \<open>Q y\<close>
  by (metis assms hoare_triple_def)

lemma precond_strengthen :
  assumes
    \<open>\<And> x. P x \<Longrightarrow> P' x\<close>
    \<open>\<turnstile>pmf \<lbrakk>P'\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  by (metis assms(1,2) hoare_tripleE hoare_tripleI) 

lemma precond_false [simp] :
  \<open>\<turnstile>pmf \<lbrakk>\<lblot>False\<rblot>\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  by (simp add: hoare_tripleI)

lemma postcond_weaken :
  assumes
    \<open>\<And> x. Q' x \<Longrightarrow> Q x\<close>
    \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q'\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  by (metis assms(1,2) hoare_tripleE hoare_tripleI) 

lemma postcond_true [simp] :
  \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>\<lblot>True\<rblot>\<rbrakk>\<close>
  by (simp add: hoare_tripleI)

(* lemma fail [simp] :
  \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> \<lblot>fail_pmf\<rblot> \<lbrakk>Q\<rbrakk>\<close>
  by (metis fail_pmf_def empty_iff hoare_tripleI set_pmf_return_pmf_None) *)

lemma skip [simp] :
  \<open>(\<turnstile>pmf \<lbrakk>P\<rbrakk> return_pmf \<lbrakk>Q\<rbrakk>) \<longleftrightarrow> (\<forall> x. P x \<longrightarrow> Q x)\<close>
  by (auto intro: hoare_tripleI elim: hoare_tripleE)

lemma skip' [simp] :
  \<open>(\<turnstile>pmf \<lbrakk>P\<rbrakk> (\<lambda> x. return_pmf (f x)) \<lbrakk>Q\<rbrakk>) \<longleftrightarrow> (\<forall> x. P x \<longrightarrow> Q (f x))\<close>
  by (simp add: hoare_triple_def)

lemma hoare_triple_altdef :
  \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<longleftrightarrow> \<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>(\<lambda> y. \<forall> x. P x \<longrightarrow> (\<turnstile>pmf f x \<Rightarrow>? y) \<longrightarrow> Q y)\<rbrakk>\<close>
  by (smt (verit, ccfv_SIG) hoare_tripleE hoare_tripleI)

lemma if_then_else :
  assumes
    \<open>\<And> x. f x \<Longrightarrow> \<turnstile>pmf \<lbrakk>(\<lambda> x'. x = x' \<and> P x)\<rbrakk> g \<lbrakk>Q\<rbrakk>\<close>
    \<open>\<And> x. \<not> f x \<Longrightarrow> \<turnstile>pmf \<lbrakk>(\<lambda> x'. x = x' \<and> P x)\<rbrakk> h \<lbrakk>Q\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> (\<lambda> x. if f x then g x else h x) \<lbrakk>Q\<rbrakk>\<close>
  using assms by (simp add: hoare_triple_def)

lemma seq :
  assumes
    \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<close>
    \<open>\<turnstile>pmf \<lbrakk>Q\<rbrakk> g \<lbrakk>R\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> (\<lambda> x. f x \<bind> g) \<lbrakk>R\<rbrakk>\<close>
  using assms by (auto intro: hoare_tripleI dest: bind_pmfE hoare_tripleE)

lemma seq' :
  assumes
    \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
    \<open>\<And> x. P x \<Longrightarrow> \<turnstile>pmf \<lbrakk>Q\<rbrakk> g x \<lbrakk>R\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> (\<lambda> x. f x \<bind> g x) \<lbrakk>R\<rbrakk>\<close>
  using assms by (smt (verit, ccfv_threshold) hoare_triple_def seq)

context
  fixes
    P :: \<open>nat \<Rightarrow> 'b \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

private abbreviation (input)
  \<open>P' index x val \<equiv>
    (index, x) \<in> set (List.enumerate offset xs) \<and>
    P index val\<close>

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
    by (fastforce
      intro!: seq[where Q = \<open>P <| Suc offset\<close>]
      simp add: hoare_triple_def add_Suc[symmetric]
      simp del: add_Suc)
qed

lemma loop :
  assumes \<open>\<And> index x. \<turnstile>pmf \<lbrakk>P' index x\<rbrakk> f x \<lbrakk>P (Suc index)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P offset\<rbrakk> foldM_pmf f xs \<lbrakk>P (offset + length xs)\<rbrakk>\<close>
  using assms
  by (auto
    intro!: loop_enumerate
    simp add: foldM_eq_foldM_enumerate[where ?offset = offset])

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile>pmf \<lbrakk>P\<rbrakk> f x \<lbrakk>P\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> foldM_pmf f xs \<lbrakk>P\<rbrakk>\<close>
  using loop[where ?P = \<open>curry <| snd >>> P\<close> and ?offset = 0] assms
  by (fastforce simp add: hoare_triple_def curry_def snd_def)

end
