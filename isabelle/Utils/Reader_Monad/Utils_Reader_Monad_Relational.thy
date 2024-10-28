theory Utils_Reader_Monad_Relational

imports
  CVM.Utils_Reader_Monad_Basic
  CVM.Utils_Reader_Monad_Hoare

begin

definition
  \<open>rel_rd R \<phi> m \<phi>' m' \<equiv>
    R \<phi> (run_reader m \<phi>) \<phi>' (run_reader m' \<phi>')\<close>

definition relational_hoare_triple
  (\<open>\<turnstile> \<lbrace> _ \<rbrace> \<langle> _ | _ \<rangle> \<lbrace> _ \<rbrace>\<close> [21, 20, 20, 21] 60) where
  \<open>(\<turnstile> \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>) \<equiv>
    \<forall> \<phi> x \<phi>' x'. R \<phi> x \<phi>' x' \<longrightarrow> rel_rd S \<phi> (f x) \<phi>' (f' x')\<close>

lemma relational_hoare_iff_hoare [simp] :
  \<open>(\<turnstile> \<lbrace>(\<lambda> \<phi> x \<phi>' x'. R \<phi> x \<and> R \<phi>' x')\<rbrace>
    \<langle>f | f\<rangle>
    \<lbrace>(\<lambda> \<phi> x \<phi>' x'. S \<phi> x \<and> S \<phi>' x')\<rbrace>)
  \<longleftrightarrow> (\<turnstile> \<lbrace>R\<rbrace> f \<lbrace>S\<rbrace>)\<close>
  by (smt (verit, best) hoare_triple_def rel_rd_def relational_hoare_triple_def)

lemma skip_left [simp] :
  \<open>(\<turnstile> \<lbrace>(\<lambda> \<phi> x \<phi>' x'. R \<phi> x \<and> R' \<phi> x \<phi>' x')\<rbrace>
    \<langle>return_rd | f\<rangle>
    \<lbrace>(\<lambda> \<phi> x \<phi>' x'. S \<phi> x \<phi>' x')\<rbrace>)
  \<longleftrightarrow> (\<forall> \<phi> x. R \<phi> x \<longrightarrow> \<turnstile> \<lbrace>R' \<phi> x\<rbrace> f \<lbrace>S \<phi> x\<rbrace>)\<close>
  by (smt (verit) hoare_triple_def rel_rd_def relational_hoare_triple_def run_reader_simps(1))

lemma skip [simp] :
  \<open>\<turnstile> \<lbrace>R\<rbrace> \<langle>return_rd | return_rd\<rangle> \<lbrace>S\<rbrace>
  \<longleftrightarrow> (\<forall> \<phi> x \<phi>' x'. R \<phi> x \<phi>' x' \<longrightarrow> S \<phi> x \<phi>' x')\<close>
  by (simp add: relational_hoare_triple_def rel_rd_def run_reader_simps(1))

lemma skip' [simp] :
  \<open>\<turnstile> \<lbrace>R\<rbrace> \<langle>(\<lambda> x. return_rd (f x)) | (\<lambda> x. return_rd (f' x))\<rangle> \<lbrace>S\<rbrace>
  \<longleftrightarrow> (\<forall> \<phi> x \<phi>' x'. R \<phi> x \<phi>' x' \<longrightarrow> S \<phi> (f x) \<phi>' (f' x'))\<close>
  by (simp add: relational_hoare_triple_def rel_rd_def run_reader_simps(1))

lemma seq :
  assumes
    \<open>\<turnstile> \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>\<close>
    \<open>\<turnstile> \<lbrace>S\<rbrace> \<langle>g | g'\<rangle> \<lbrace>T\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>R\<rbrace> \<langle>(f >=> g) | (f' >=> g')\<rangle> \<lbrace>T\<rbrace>\<close>
  using assms by (simp add: rel_rd_def relational_hoare_triple_def run_reader_simps(3))

lemma seq' :
  assumes
    \<open>\<turnstile> \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>\<close>
    \<open>\<And> \<phi> x \<phi>' x'. R \<phi> x \<phi>' x' \<Longrightarrow> \<turnstile> \<lbrace>S\<rbrace> \<langle>g x | g' x'\<rangle> \<lbrace>T\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>R\<rbrace> \<langle>(\<lambda> x. (x |> (f >=> g x))) | (\<lambda> x. (x |> (f' >=> g' x)))\<rangle> \<lbrace>T\<rbrace>\<close>
  using assms by (simp add: rel_rd_def relational_hoare_triple_def run_reader_simps(3))

context
  fixes
    R :: \<open>nat \<Rightarrow> 'b \<Rightarrow>'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

abbreviation (input)
  \<open>foldM_enumerate' fn \<equiv> foldM_rd_enumerate fn xs offset\<close>

abbreviation (input)
  \<open>R' index \<phi> val \<phi>' val' \<equiv> index < offset + length xs \<and> R index \<phi> val \<phi>' val'\<close>

lemma loop_enumerate :
  \<open>(\<And> index x. \<turnstile> \<lbrace>R' index\<rbrace> \<langle>f (index, x) | f' (index, x)\<rangle> \<lbrace>R (Suc index)\<rbrace>)
    \<Longrightarrow> \<turnstile> \<lbrace>R offset\<rbrace>
        \<langle>foldM_enumerate' f | foldM_enumerate' f'\<rangle>
        \<lbrace>R (offset + length xs)\<rbrace>\<close>
proof (induction xs arbitrary: offset)
  case Nil
  then show ?case by (simp add: foldM_enumerate_def)
next
  case (Cons _ _)
  then show ?case
    apply (simp add: foldM_enumerate_def)
    by (fastforce
      intro!: seq[where S = \<open>R <| Suc offset\<close>]
      simp add: relational_hoare_triple_def add_Suc[symmetric]
      simp del: add_Suc)
qed

lemma loop :
  assumes \<open>\<And> index x. \<turnstile> \<lbrace>R' index\<rbrace> \<langle>f x | f' x\<rangle> \<lbrace>R (Suc index)\<rbrace>\<close>
  shows
    \<open>\<turnstile> \<lbrace>R offset\<rbrace>
      \<langle>foldM_rd f xs | foldM_rd f' xs\<rangle>
      \<lbrace>R (offset + length xs)\<rbrace>\<close>
  using assms
  by (auto
    intro: loop_enumerate
    simp add: foldM_eq_foldM_enumerate[where ?offset = offset])

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile> \<lbrace>R\<rbrace> \<langle>f x | f' x\<rangle> \<lbrace>R\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>R\<rbrace> \<langle>foldM_rd f xs | foldM_rd f' xs\<rangle> \<lbrace>R\<rbrace>\<close>
  using loop[where ?R = \<open>\<lambda> _ x. R x\<close>, where ?offset = 0] assms
  by (fastforce simp add: relational_hoare_triple_def curry_def snd_def)

end