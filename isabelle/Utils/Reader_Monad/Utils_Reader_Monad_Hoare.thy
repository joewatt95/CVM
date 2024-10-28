theory Utils_Reader_Monad_Hoare

imports
  CVM.Utils_Function
  CVM.Utils_Reader_Monad_Basic

begin

definition hoare_triple ::
  \<open>['a \<Rightarrow> 'b \<Rightarrow> bool, 'b \<Rightarrow> ('a, 'c) reader_monad, 'a \<Rightarrow> 'c \<Rightarrow> bool] \<Rightarrow> bool\<close>
  (\<open>\<turnstile> \<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv>
    \<forall> \<phi> x. P \<phi> x \<longrightarrow> Q \<phi> (run_reader (f x) \<phi>)\<close>

lemma hoare_tripleI :
  assumes \<open>\<And> \<phi> x. P \<phi> x \<Longrightarrow> Q \<phi> (run_reader (f x) \<phi>)\<close>
  shows \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  by (simp add: assms hoare_triple_def)

lemma hoare_tripleE :
  assumes
    \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
    \<open>P \<phi> x\<close>
  shows \<open>Q \<phi> (run_reader (f x) \<phi>)\<close>
  by (metis assms hoare_triple_def)

lemma precond_postcond :
  assumes
    \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
    \<open>\<And> \<phi> x. P' \<phi> x \<Longrightarrow> P \<phi> x\<close>
    \<open>\<And> \<phi> y. Q \<phi> y \<Longrightarrow> Q' \<phi> y\<close>
  shows \<open>\<turnstile> \<lbrace>P'\<rbrace> f \<lbrace>Q'\<rbrace>\<close>
  by (metis assms hoare_tripleI hoare_tripleE)

lemma postcond_true :
  \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrace>\<close>
  by (simp add: hoare_tripleI)

lemma get_rd :
  fixes P
  defines \<open>P' \<equiv> \<lambda> \<phi> _. P \<phi>\<close>
  shows \<open>\<turnstile> \<lbrace>P'\<rbrace> \<lblot>get_rd\<rblot> \<lbrace>P'\<rbrace>\<close>
  by (simp add: assms hoare_triple_def run_reader_simps)

lemma skip [simp] :
  \<open>(\<turnstile> \<lbrace>P\<rbrace> return_rd \<lbrace>Q\<rbrace>) \<longleftrightarrow> (\<forall> \<phi> x. P \<phi> x \<longrightarrow> Q \<phi> x)\<close>
  by (simp add: hoare_triple_def run_reader_simps(1))

lemma skip' [simp] :
  \<open>(\<turnstile> \<lbrace>P\<rbrace> (\<lambda> x. return_rd (f x)) \<lbrace>Q\<rbrace>) \<longleftrightarrow> (\<forall> \<phi> x. P \<phi> x \<longrightarrow> Q \<phi> (f x))\<close>
  by (simp add: hoare_triple_def run_reader_simps(1))

lemma if_then_else :
  assumes
    \<open>\<And> b. f b \<Longrightarrow> \<turnstile> \<lbrace>P\<rbrace> g \<lbrace>Q\<rbrace>\<close>
    \<open>\<And> b. \<not> f b \<Longrightarrow> \<turnstile> \<lbrace>P\<rbrace> h \<lbrace>Q\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>P\<rbrace> (\<lambda> b. if f b then g b else h b) \<lbrace>Q\<rbrace>\<close>
  using assms by (simp add: hoare_triple_def)

lemma seq :
  assumes
    \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
    \<open>\<turnstile> \<lbrace>Q\<rbrace> g \<lbrace>R\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>P\<rbrace> f >=> g \<lbrace>R\<rbrace>\<close>
  using assms
  by (simp add: hoare_triple_def run_reader_simps(3))

lemma seq' :
  assumes
    \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
    \<open>\<And> \<phi> x. P \<phi> x \<Longrightarrow> \<turnstile> \<lbrace>Q\<rbrace> g x \<lbrace>R\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>P\<rbrace> (\<lambda> x. (x |> (f >=> g x))) \<lbrace>R\<rbrace>\<close>
  using assms by (simp add: hoare_triple_def run_reader_simps(3))

context
  fixes
    P :: \<open>nat \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

abbreviation (input)
  \<open>P' index \<phi> val \<equiv> index < offset + length xs \<and> P index \<phi> val\<close>

lemma loop_enumerate :
  \<open>(\<And> index x. \<turnstile> \<lbrace>P' index\<rbrace> f (index, x) \<lbrace>P (Suc index)\<rbrace>)
    \<Longrightarrow> \<turnstile> \<lbrace>P offset\<rbrace>
          foldM_rd_enumerate f xs offset
          \<lbrace>P (offset + length xs)\<rbrace>\<close>
proof (induction xs arbitrary: offset)
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
  assumes \<open>\<And> index x. \<turnstile> \<lbrace>P' index\<rbrace> f x \<lbrace>P (Suc index)\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>P offset\<rbrace> foldM_rd f xs \<lbrace>P (offset + length xs)\<rbrace>\<close>
  using assms
  by (auto
    intro: loop_enumerate
    simp add: foldM_eq_foldM_enumerate[where ?offset = offset])

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile> \<lbrace>P\<rbrace> f x \<lbrace>P\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>P\<rbrace> foldM_rd f xs \<lbrace>P\<rbrace>\<close>
  using loop[where ?P = \<open>curry <| snd >>> P\<close>, where ?offset = 0] assms
  by (fastforce simp add: hoare_triple_def curry_def snd_def)

end