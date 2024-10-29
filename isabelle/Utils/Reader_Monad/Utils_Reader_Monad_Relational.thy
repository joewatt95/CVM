theory Utils_Reader_Monad_Relational

imports
  CVM.Utils_Reader_Monad_Basic
  CVM.Utils_Reader_Monad_Hoare

begin

definition
  \<open>rel_rd R \<phi> m \<phi>' m' \<equiv>
    R \<phi> (run_reader m \<phi>) \<phi>' (run_reader m' \<phi>')\<close>

definition relational_hoare_triple
  (\<open>\<turnstile>rd \<lbrakk> _ \<rbrakk> \<langle> _ | _ \<rangle> \<lbrakk> _ \<rbrakk>\<close> [21, 20, 20, 21] 60) where
  \<open>(\<turnstile>rd \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>S\<rbrakk>) \<equiv>
    \<forall> \<phi> x \<phi>' x'. R \<phi> x \<phi>' x' \<longrightarrow> rel_rd S \<phi> (f x) \<phi>' (f' x')\<close>

lemma relational_hoare_iff_hoare [simp] :
  \<open>(\<turnstile>rd \<lbrakk>(\<lambda> \<phi> x \<phi>' x'. R \<phi> x \<and> R \<phi>' x')\<rbrakk>
    \<langle>f | f\<rangle>
    \<lbrakk>(\<lambda> \<phi> x \<phi>' x'. S \<phi> x \<and> S \<phi>' x')\<rbrakk>)
  \<longleftrightarrow> (\<turnstile>rd \<lbrakk>R\<rbrakk> f \<lbrakk>S\<rbrakk>)\<close>
  by (smt (verit, best) hoare_triple_def rel_rd_def relational_hoare_triple_def)

lemma skip [simp] :
  \<open>\<turnstile>rd \<lbrakk>R\<rbrakk> \<langle>return_rd | return_rd\<rangle> \<lbrakk>S\<rbrakk>
  \<longleftrightarrow> (\<forall> \<phi> x \<phi>' x'. R \<phi> x \<phi>' x' \<longrightarrow> S \<phi> x \<phi>' x')\<close>

  \<open>(\<turnstile>rd \<lbrakk>(\<lambda> \<phi> x \<phi>' x'. R \<phi> x \<phi>' x')\<rbrakk>
    \<langle>return_rd | f\<rangle>
    \<lbrakk>(\<lambda> \<phi> x \<phi>' x'. S \<phi> x \<phi>' x')\<rbrakk>)
  \<longleftrightarrow> (\<forall> \<phi> x. \<turnstile>rd \<lbrakk>R \<phi> x\<rbrakk> f \<lbrakk>S \<phi> x\<rbrakk>)\<close>

  \<open>(\<turnstile>rd \<lbrakk>(\<lambda> \<phi> x \<phi>' x'. R \<phi> x \<phi>' x')\<rbrakk>
    \<langle>f | return_rd\<rangle>
    \<lbrakk>(\<lambda> \<phi> x \<phi>' x'. S \<phi> x \<phi>' x')\<rbrakk>)
  \<longleftrightarrow> (\<forall> \<phi>' x'. \<turnstile>rd \<lbrakk>(\<lambda> \<phi> x. R \<phi> x \<phi>' x')\<rbrakk> f \<lbrakk>(\<lambda> \<phi> x. S \<phi> x \<phi>' x')\<rbrakk>)\<close>
  by (auto simp add: relational_hoare_triple_def hoare_triple_def rel_rd_def run_reader_simps(1))

lemma skip' [simp] :
  \<open>\<turnstile>rd \<lbrakk>R\<rbrakk> \<langle>(\<lambda> x. return_rd (f x)) | (\<lambda> x. return_rd (f' x))\<rangle> \<lbrakk>S\<rbrakk>
  \<longleftrightarrow> (\<forall> \<phi> x \<phi>' x'. R \<phi> x \<phi>' x' \<longrightarrow> S \<phi> (f x) \<phi>' (f' x'))\<close>
  by (simp add: relational_hoare_triple_def rel_rd_def run_reader_simps(1))

lemma seq :
  assumes
    \<open>\<turnstile>rd \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>S\<rbrakk>\<close>
    \<open>\<turnstile>rd \<lbrakk>S\<rbrakk> \<langle>g | g'\<rangle> \<lbrakk>T\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>R\<rbrakk> \<langle>f >=> g | f' >=> g'\<rangle> \<lbrakk>T\<rbrakk>\<close>
  using assms by (simp add: rel_rd_def relational_hoare_triple_def run_reader_simps(3))

lemma skip_seq :
  assumes
    \<open>\<turnstile>rd \<lbrakk>R\<rbrakk> \<langle>f | f\<rangle> \<lbrakk>S\<rbrakk>\<close>
    \<open>\<And> \<phi> x. \<turnstile>rd \<lbrakk>S \<phi> x\<rbrakk> g \<lbrakk>T \<phi> x\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>R\<rbrakk> \<langle>f | f >=> g\<rangle> \<lbrakk>T\<rbrakk>\<close>
  by (smt (verit, best) assms(1,2) hoare_tripleE rel_rd_def relational_hoare_triple_def run_reader_simps(3))

lemma seq_skip :
  assumes
    \<open>\<turnstile>rd \<lbrakk>R\<rbrakk> \<langle>f | f\<rangle> \<lbrakk>S\<rbrakk>\<close>
    \<open>\<And> \<phi>' x'. \<turnstile>rd \<lbrakk>(\<lambda> \<phi> x. S \<phi> x \<phi>' x')\<rbrakk> g \<lbrakk>(\<lambda> \<phi> x. T \<phi> x \<phi>' x')\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>R\<rbrakk> \<langle>f >=> g | f\<rangle> \<lbrakk>T\<rbrakk>\<close>
  by (smt (verit) assms(1,2) hoare_triple_def rel_rd_def relational_hoare_triple_def run_reader_simps(3))

lemma seq' :
  assumes
    \<open>\<turnstile>rd \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>S\<rbrakk>\<close>
    \<open>\<And> \<phi> x \<phi>' x'. R \<phi> x \<phi>' x' \<Longrightarrow> \<turnstile>rd \<lbrakk>S\<rbrakk> \<langle>g x | g' x'\<rangle> \<lbrakk>T\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>R\<rbrakk> \<langle>(\<lambda> x. (x |> (f >=> g x))) | (\<lambda> x. (x |> (f' >=> g' x)))\<rangle> \<lbrakk>T\<rbrakk>\<close>
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
  \<open>(\<And> index x. \<turnstile>rd \<lbrakk>R' index\<rbrakk> \<langle>f (index, x) | f' (index, x)\<rangle> \<lbrakk>R (Suc index)\<rbrakk>) \<Longrightarrow>
  \<turnstile>rd \<lbrakk>R offset\<rbrakk>
      \<langle>foldM_enumerate' f | foldM_enumerate' f'\<rangle>
      \<lbrakk>R (offset + length xs)\<rbrakk>\<close>
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
  assumes \<open>\<And> index x. \<turnstile>rd \<lbrakk>R' index\<rbrakk> \<langle>f x | f' x\<rangle> \<lbrakk>R (Suc index)\<rbrakk>\<close>
  shows \<open>\<turnstile>rd
    \<lbrakk>R offset\<rbrakk>
    \<langle>foldM_rd f xs | foldM_rd f' xs\<rangle>
    \<lbrakk>R (offset + length xs)\<rbrakk>\<close>
  using assms
  by (auto
    intro: loop_enumerate
    simp add: foldM_eq_foldM_enumerate[where ?offset = offset])

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile>rd \<lbrakk>R\<rbrakk> \<langle>f x | f' x\<rangle> \<lbrakk>R\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>R\<rbrakk> \<langle>foldM_rd f xs | foldM_rd f' xs\<rangle> \<lbrakk>R\<rbrakk>\<close>
  using loop[where ?R = \<open>\<lambda> _ x. R x\<close>, where ?offset = 0] assms
  by (fastforce simp add: relational_hoare_triple_def curry_def snd_def)

end