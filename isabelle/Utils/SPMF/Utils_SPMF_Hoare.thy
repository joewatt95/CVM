theory Utils_SPMF_Hoare

(*
Specialisation of Lean's SatisfiesM to the SPMF monad.
This enables Hoare-logic-like reasoning for the partial correctness of spmf
monadic programs.

References:
https://leanprover-community.github.io/mathlib4_docs/Batteries/Classes/SatisfiesM.html
https://link.springer.com/content/pdf/10.1007/3-540-36578-8_19.pdf
https://personal.cis.strath.ac.uk/conor.mcbride/Kleisli.pdf
*)

imports
  CVM.Utils_SPMF_FoldM

begin

abbreviation possibly_evals_to
  (\<open>\<turnstile> _ \<Rightarrow>? _\<close> [20, 2] 60) where
  \<open>\<turnstile> p \<Rightarrow>? x \<equiv> x \<in> set_spmf p\<close>

lemma bind_spmfE :
  assumes \<open>\<turnstile> f x \<bind> g \<Rightarrow>? z\<close>
  obtains y where
    \<open>\<turnstile> f x \<Rightarrow>? y\<close>
    \<open>\<turnstile> g y \<Rightarrow>? z\<close>
  using assms by (auto simp add: set_bind_spmf)

definition hoare_triple ::
  \<open>['a \<Rightarrow> bool, 'a \<Rightarrow> 'b spmf, 'b \<Rightarrow> bool] \<Rightarrow> bool\<close>
  (\<open>\<turnstile> \<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> \<forall> x y. P x \<longrightarrow> (\<turnstile> f x \<Rightarrow>? y) \<longrightarrow> Q y\<close>

lemma hoare_tripleI :
  assumes \<open>\<And> x y. \<lbrakk>P x; \<turnstile> f x \<Rightarrow>? y\<rbrakk> \<Longrightarrow> Q y\<close>
  shows \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  by (metis assms hoare_triple_def)

lemma hoare_tripleE :
  assumes
    \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
    \<open>P x\<close>
    \<open>\<turnstile> f x \<Rightarrow>? y\<close>
  shows \<open>Q y\<close>
  by (metis assms hoare_triple_def)

lemma precond_strengthen :
  assumes
    \<open>\<And> x. P x \<Longrightarrow> P' x\<close>
    \<open>\<turnstile> \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  by (metis assms(1,2) hoare_tripleE hoare_tripleI) 

lemma precond_false :
  \<open>\<turnstile> \<lbrace>\<lblot>False\<rblot>\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  by (simp add: hoare_tripleI)

lemma postcond_weaken :
  assumes
    \<open>\<And> x. Q' x \<Longrightarrow> Q x\<close>
    \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  by (metis assms(1,2) hoare_tripleE hoare_tripleI) 

lemma postcond_true :
  \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>\<lblot>True\<rblot>\<rbrace>\<close>
  by (simp add: hoare_tripleI)

lemma fail [simp] :
  \<open>\<turnstile> \<lbrace>P\<rbrace> \<lblot>fail_spmf\<rblot> \<lbrace>Q\<rbrace>\<close>
  by (metis fail_spmf_def empty_iff hoare_tripleI set_spmf_return_pmf_None)

lemma skip [simp] :
  \<open>(\<turnstile> \<lbrace>P\<rbrace> return_spmf \<lbrace>Q\<rbrace>) \<longleftrightarrow> (\<forall> x. P x \<longrightarrow> Q x)\<close>
  by (auto intro: hoare_tripleI elim: hoare_tripleE)

lemma skip' [simp] :
  \<open>(\<turnstile> \<lbrace>P\<rbrace> (\<lambda> x. return_spmf (f x)) \<lbrace>Q\<rbrace>) \<longleftrightarrow> (\<forall> x. P x \<longrightarrow> Q (f x))\<close>
  by (simp add: hoare_triple_def)

lemma hoare_triple_altdef :
  \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<longleftrightarrow> \<turnstile> \<lbrace>P\<rbrace> f \<lbrace>(\<lambda> y. \<forall> x. P x \<longrightarrow> (\<turnstile> f x \<Rightarrow>? y) \<longrightarrow> Q y)\<rbrace>\<close>
  by (smt (verit, ccfv_SIG) hoare_tripleE hoare_tripleI)

lemma if_then_else :
  assumes
    \<open>\<And> x. f x \<Longrightarrow> \<turnstile> \<lbrace>(\<lambda> x'. x = x' \<and> P x)\<rbrace> g \<lbrace>Q\<rbrace>\<close>
    \<open>\<And> x. \<not> f x \<Longrightarrow> \<turnstile> \<lbrace>(\<lambda> x'. x = x' \<and> P x)\<rbrace> h \<lbrace>Q\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>P\<rbrace> (\<lambda> x. if f x then g x else h x) \<lbrace>Q\<rbrace>\<close>
  using assms by (simp add: hoare_triple_def)

lemma seq :
  assumes
    \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<close>
    \<open>\<turnstile> \<lbrace>Q\<rbrace> g \<lbrace>R\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>P\<rbrace> f >=> g \<lbrace>R\<rbrace>\<close>
  using assms by (auto intro: hoare_tripleI dest: bind_spmfE hoare_tripleE)

lemma seq' :
  assumes
    \<open>\<turnstile> \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
    \<open>\<And> x. P x \<Longrightarrow> \<turnstile> \<lbrace>Q\<rbrace> g x \<lbrace>R\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>P\<rbrace> (\<lambda> x. (x |> (f >=> g x))) \<lbrace>R\<rbrace>\<close>
  using assms by (smt (verit, ccfv_threshold) hoare_triple_def seq)

context
  fixes
    P :: \<open>nat \<Rightarrow> 'b \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

abbreviation (input)
  \<open>P' index val \<equiv> index < offset + length xs \<and> P index val\<close>

lemma loop_enumerate :
  \<open>(\<And> index x. \<turnstile> \<lbrace>P' index\<rbrace> f (index, x) \<lbrace>P (Suc index)\<rbrace>)
    \<Longrightarrow> \<turnstile> \<lbrace>P offset\<rbrace>
          foldM_spmf_enumerate f xs offset
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
  shows \<open>\<turnstile> \<lbrace>P offset\<rbrace> foldM_spmf f xs \<lbrace>P (offset + length xs)\<rbrace>\<close>
  using assms
  by (auto
    intro: loop_enumerate
    simp add: foldM_eq_foldM_enumerate[where ?offset = offset])

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile> \<lbrace>P\<rbrace> f x \<lbrace>P\<rbrace>\<close>
  shows \<open>\<turnstile> \<lbrace>P\<rbrace> foldM_spmf f xs \<lbrace>P\<rbrace>\<close>
  using loop[where ?P = \<open>curry <| snd >>> P\<close>, where ?offset = 0] assms
  by (fastforce simp add: hoare_triple_def curry_def snd_def)

lemma integral_mono_of_hoare_triple :
  fixes
    x :: 'a and
    f :: \<open>'a \<Rightarrow> 'b spmf\<close> and
    g h :: \<open>'b \<Rightarrow> real\<close>
  defines \<open>\<mu> \<equiv> measure_spmf (f x)\<close>
  assumes
    \<open>\<turnstile> \<lbrace>\<lblot>True\<rblot>\<rbrace> f \<lbrace>(\<lambda> y. g y \<le> h y)\<rbrace>\<close>
    \<open>integrable \<mu> g\<close>
    \<open>integrable \<mu> h\<close>
  shows \<open>(\<integral> y. g y \<partial> \<mu>) \<le> \<integral> y. h y \<partial> \<mu>\<close>

  using assms by (auto intro!: integral_mono_AE elim!: hoare_tripleE)

lemma prob_fail_foldM_spmf_le :
  fixes
    p :: real and
    P :: \<open>'b \<Rightarrow> bool\<close>
  assumes
    \<open>\<And> x. \<turnstile> \<lbrace>P\<rbrace> f x \<lbrace>P\<rbrace>\<close>
    \<open>\<And> x val. P val \<Longrightarrow> prob_fail (f x val) \<le> p\<close>
  shows \<open>P val \<Longrightarrow> prob_fail (foldM_spmf f xs val) \<le> length xs * p\<close>
proof (induction xs arbitrary: val)
  case Nil
  then show ?case by (simp add: prob_fail_def)
next
  case (Cons x xs)

  let ?val' = \<open>f x val\<close>
  let ?\<mu>' = \<open>measure_spmf ?val'\<close>

  have
    \<open>prob_fail (foldM_spmf f (x # xs) val)
    = prob_fail ?val' + \<integral> val'. prob_fail (foldM_spmf f xs val') \<partial> ?\<mu>'\<close>
    by (simp add: prob_fail_def pmf_bind_spmf_None)

  also have \<open>... \<le> p + \<integral> _. length xs * p \<partial> ?\<mu>'\<close>
  proof -
    have \<open>\<turnstile>
      \<lbrace>\<lblot>\<top>\<rblot>\<rbrace> \<lblot>?val'\<rblot>
      \<lbrace>(\<lambda> val'. prob_fail (foldM_spmf f xs val') \<le> length xs * p)\<rbrace>\<close>
      using assms Cons.IH \<open>P val\<close>
      by (smt (verit, ccfv_threshold) hoare_tripleE hoare_tripleI skip)

    then have
      \<open>(\<integral> val'. prob_fail (foldM_spmf f xs val') \<partial> ?\<mu>')
      \<le> \<integral> _. length xs * p \<partial> ?\<mu>'\<close>
      apply (intro integral_mono_of_hoare_triple[where f = \<open>\<lblot>?val'\<rblot>\<close>])
      using assms integrable_prob_fail_foldM_spmf by auto

    moreover have \<open>prob_fail ?val' \<le> p\<close> using \<open>P val\<close> assms by simp

    ultimately show ?thesis by simp
  qed

  also have \<open>... \<le> p + length xs * p\<close>
  proof -
    have \<open>p \<ge> 0 \<Longrightarrow> ?thesis\<close>
      by (auto simp add: landau_omega.R_mult_right_mono mult_le_cancel_right2 weight_spmf_le_1)

    then show ?thesis
      by (metis Cons.prems assms(2) dual_order.trans pmf_nonneg prob_fail_def)
  qed

  finally show ?case by (simp add: distrib_left mult.commute) 
qed

end