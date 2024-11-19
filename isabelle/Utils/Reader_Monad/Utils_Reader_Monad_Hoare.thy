(* Hoare logic on reader monad, stolen from:
https://trustworthy.systems/publications/nicta_full_text/483.pdf
*)
theory Utils_Reader_Monad_Hoare

imports
  CVM.Utils_Function
  CVM.Utils_Reader_Monad_Basic

begin

definition hoare_triple ::
  \<open>['a \<Rightarrow> 'b \<Rightarrow> bool, 'b \<Rightarrow> ('a, 'c) reader_monad, 'a \<Rightarrow> 'c \<Rightarrow> bool] \<Rightarrow> bool\<close>
  (\<open>\<turnstile>rd \<lbrakk> _ \<rbrakk> _ \<lbrakk> _ \<rbrakk> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<equiv>
    \<forall> \<phi> x. P \<phi> x \<longrightarrow> Q \<phi> (run_reader (f x) \<phi>)\<close>

lemma hoare_tripleI :
  assumes \<open>\<And> \<phi> x. P \<phi> x \<Longrightarrow> Q \<phi> (run_reader (f x) \<phi>)\<close>
  shows \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  by (simp add: assms hoare_triple_def)

lemma hoare_tripleE :
  assumes
    \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
    \<open>P \<phi> x\<close>
  shows \<open>Q \<phi> (run_reader (f x) \<phi>)\<close>
  by (metis assms hoare_triple_def)

lemma precond_strengthen :
  assumes
    \<open>\<And> \<phi> x. P \<phi> x \<Longrightarrow> P' \<phi> x\<close>
    \<open>\<turnstile>rd \<lbrakk>P'\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  by (metis assms(1,2) hoare_tripleE hoare_tripleI) 

lemma precond_false :
  \<open>\<turnstile>rd \<lbrakk>\<lblot>\<lblot>False\<rblot>\<rblot>\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  by (simp add: hoare_tripleI)

lemma postcond_weaken :
  assumes
    \<open>\<And> \<phi> x. Q' \<phi> x \<Longrightarrow> Q \<phi> x\<close>
    \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> f \<lbrakk>Q'\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
  by (metis assms(1,2) hoare_tripleE hoare_tripleI) 

lemma postcond_true :
  \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> f \<lbrakk>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrakk>\<close>
  by (simp add: hoare_tripleI)

lemma get_rd :
  \<open>\<turnstile>rd \<lbrakk>(\<lambda> \<phi>. \<lblot>P \<phi> \<phi>\<rblot>)\<rbrakk> \<lblot>get_rd\<rblot> \<lbrakk>P\<rbrakk>\<close>
  by (simp add: hoare_triple_def run_reader_simps)

lemma skip [simp] :
  \<open>(\<turnstile>rd \<lbrakk>P\<rbrakk> return_rd \<lbrakk>Q\<rbrakk>) \<longleftrightarrow> (\<forall> \<phi> x. P \<phi> x \<longrightarrow> Q \<phi> x)\<close>
  by (simp add: hoare_triple_def run_reader_simps(1))

lemma skip' [simp] :
  \<open>(\<turnstile>rd \<lbrakk>P\<rbrakk> (\<lambda> x. return_rd (f x)) \<lbrakk>Q\<rbrakk>) \<longleftrightarrow> (\<forall> \<phi> x. P \<phi> x \<longrightarrow> Q \<phi> (f x))\<close>
  by (simp add: hoare_triple_def run_reader_simps(1))

lemma if_then_else :
  assumes
    \<open>\<And> x. f x \<Longrightarrow> \<turnstile>rd \<lbrakk>(\<lambda> \<phi> x'. x = x' \<and> P \<phi> x)\<rbrakk> g \<lbrakk>Q\<rbrakk>\<close>
    \<open>\<And> x. \<not> f x \<Longrightarrow> \<turnstile>rd \<lbrakk>(\<lambda> \<phi> x'. x = x' \<and> P \<phi> x)\<rbrakk> h \<lbrakk>Q\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> (\<lambda> x. if f x then g x else h x) \<lbrakk>Q\<rbrakk>\<close>
  by (smt (verit, best) assms(1,2) hoare_tripleE hoare_tripleI)

lemma seq :
  assumes
    \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
    \<open>\<turnstile>rd \<lbrakk>Q\<rbrakk> g \<lbrakk>R\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> f >=> g \<lbrakk>R\<rbrakk>\<close>
  using assms
  by (simp add: hoare_triple_def run_reader_simps(3))

lemma seq' :
  assumes
    \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk>\<close>
    \<open>\<And> \<phi> x. P \<phi> x \<Longrightarrow> \<turnstile>rd \<lbrakk>Q\<rbrakk> g x \<lbrakk>R\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> (\<lambda> x. (x |> (f >=> g x))) \<lbrakk>R\<rbrakk>\<close>
  using assms by (simp add: hoare_triple_def run_reader_simps(3))

context
  fixes
    P :: \<open>nat \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

private abbreviation (input)
  \<open>P' index x \<phi> val \<equiv>
    (index, x) \<in> set (List.enumerate offset xs) \<and>
    P index \<phi> val\<close>

lemma loop_enumerate :
  assumes \<open>\<And> index x. \<turnstile>rd \<lbrakk>P' index x\<rbrakk> f (index, x) \<lbrakk>P (Suc index)\<rbrakk>\<close>
  shows \<open> \<turnstile>rd
    \<lbrakk>P offset\<rbrakk>
    foldM_rd_enumerate f xs offset
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
  assumes \<open>\<And> index x. \<turnstile>rd \<lbrakk>P' index x\<rbrakk> f x \<lbrakk>P (Suc index)\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>P offset\<rbrakk> foldM_rd f xs \<lbrakk>P (offset + length xs)\<rbrakk>\<close>
  using assms
  by (auto
    intro: loop_enumerate
    simp add: foldM_eq_foldM_enumerate[where ?offset = offset])

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile>rd \<lbrakk>P\<rbrakk> f x \<lbrakk>P\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> foldM_rd f xs \<lbrakk>P\<rbrakk>\<close>
  using loop[where ?P = \<open>curry <| snd >>> P\<close>, where ?offset = 0] assms
  by (fastforce simp add: hoare_triple_def curry_def snd_def)

end