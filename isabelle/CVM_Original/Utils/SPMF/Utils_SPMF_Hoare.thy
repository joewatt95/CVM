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
  Probabilistic_While.While_SPMF
  Utils_SPMF_FoldM
  Utils_PMF_Hoare

begin

(* abbreviation possibly_evals_to
  (\<open>\<turnstile>spmf _ \<Rightarrow>? _\<close> [20, 2] 60) where
  \<open>\<turnstile>spmf p \<Rightarrow>? x \<equiv> x \<in> set_spmf p\<close> *)

(* lemma bind_spmfE :
  assumes \<open>\<turnstile>spmf f x \<bind> g \<Rightarrow>? z\<close>
  obtains y where
    \<open>\<turnstile>spmf f x \<Rightarrow>? y\<close>
    \<open>\<turnstile>spmf g y \<Rightarrow>? z\<close>
  using assms by auto *)

definition hoare_triple ::
  \<open>['a \<Rightarrow> bool, 'a \<Rightarrow> 'b spmf, 'b \<Rightarrow> bool] \<Rightarrow> bool\<close>
  (\<open>\<turnstile>spmf \<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> \<forall> x y. P x \<longrightarrow> y \<in> set_spmf (f x) \<longrightarrow> Q y\<close>

definition hoare_triple_total ::
  \<open>['a \<Rightarrow> bool, 'a \<Rightarrow> 'b spmf, 'b \<Rightarrow> bool] \<Rightarrow> bool\<close>
  (\<open>\<turnstile>spmf \<lbrakk> _ \<rbrakk> _ \<lbrakk> _ \<rbrakk>\<close> [21, 20, 21] 60) where
  \<open>\<turnstile>spmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<equiv> \<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>is_Some_and_pred Q\<rbrakk>\<close>

lemma hoare_triple_altdef :
  \<open>(\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<longleftrightarrow> (\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>is_None_or_pred Q\<rbrakk>)\<close>
  by (simp
    add: hoare_triple_def Utils_PMF_Hoare.hoare_triple_def in_set_spmf
    split: option.splits)

lemma hoare_tripleI :
  assumes \<open>\<And> x y. \<lbrakk>P x; y \<in> set_spmf (f x)\<rbrakk> \<Longrightarrow> Q y\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  by (metis assms hoare_triple_def)

lemma hoare_tripleE :
  assumes
    \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
    \<open>P x\<close>
    \<open>y \<in> set_spmf (f x)\<close>
  shows \<open>Q y\<close>
  by (metis assms hoare_triple_def)

lemma seq :
  assumes
    \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<close>
    \<open>\<turnstile>spmf \<lbrace>Q\<rbrace> g \<lbrace>R\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f >=> g \<lbrace>R\<rbrace>\<close>
  using assms by (auto simp add: hoare_triple_def set_bind_spmf)

lemma seq' :
  assumes
    \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
    \<open>\<And> x. P x \<Longrightarrow> \<turnstile>spmf \<lbrace>Q\<rbrace> g x \<lbrace>R\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> (\<lambda> x. (x |> (f >=> g x))) \<lbrace>R\<rbrace>\<close>
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

lemma loop_enumerate' :
  assumes \<open>\<And> index x. \<turnstile>spmf \<lbrace>P' index x\<rbrace> f (index, x) \<lbrace>P (Suc index)\<rbrace>\<close>
  shows \<open>\<turnstile>spmf
    \<lbrace>P offset\<rbrace>
    foldM_spmf_enumerate f xs offset
    \<lbrace>P (offset + length xs)\<rbrace>\<close>
using assms proof (induction xs arbitrary: offset)
  case Nil
  then show ?case by (simp add: foldM_enumerate_def hoare_triple_def)
next
  case (Cons _ _)
  then show ?case
    apply (simp add: foldM_enumerate_def)
    by (fastforce
      intro!: seq[where Q = \<open>P <| Suc offset\<close>] simp add: hoare_triple_def)
qed

lemma loop' :
  assumes \<open>\<And> index x. \<turnstile>spmf \<lbrace>P' index x\<rbrace> f x \<lbrace>P (Suc index)\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P offset\<rbrace> foldM_spmf f xs \<lbrace>P (offset + length xs)\<rbrace>\<close>
  using assms
  by (auto
    intro!: loop_enumerate'
    simp add: foldM_eq_foldM_enumerate[where ?offset = offset])

end

lemmas loop_enumerate = loop_enumerate'[where offset = 0, simplified]

lemmas loop = loop'[where offset = 0, simplified]

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile>spmf \<lbrace>P\<rbrace> f x \<lbrace>P\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> foldM_spmf f xs \<lbrace>P\<rbrace>\<close>
  using loop[where ?P = \<open>curry <| snd >>> P\<close>] assms
  apply (simp add: hoare_triple_def)
  by blast

lemma admissible_hoare_triple [simp] :
  \<open>spmf.admissible <| \<lambda> f. \<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  by (simp add: hoare_triple_def)

lemma while :
  assumes \<open>\<And> x. guard x \<Longrightarrow> \<turnstile>spmf \<lbrace>(\<lambda> x'. x = x' \<and> P x)\<rbrace> body \<lbrace>P\<rbrace>\<close>
  defines
    \<open>while_triple postcond \<equiv> \<turnstile>spmf \<lbrace>P\<rbrace> loop_spmf.while guard body \<lbrace>postcond\<rbrace>\<close>
  shows
    \<open>while_triple (\<lambda> x. \<not> guard x \<and> P x)\<close> (is ?thesis_0) 
    \<open>while_triple P\<close> (is ?thesis_1)
proof -
  show ?thesis_0
  unfolding while_triple_def
  proof (induction rule: loop_spmf.while_fixp_induct)
    case 1 show ?case by simp
  next
    case 2 show ?case by (simp add: Utils_SPMF_Hoare.hoare_triple_def)
  next
    case 3
    with assms show ?case
      by (smt (verit, ccfv_threshold) Utils_SPMF_Hoare.hoare_triple_def Utils_SPMF_Hoare.seq set_return_spmf singletonD)
  qed

  then show ?thesis_1 by (simp add: while_triple_def hoare_triple_def)
qed

lemma prob_fail_foldM_spmf_le :
  fixes
    p :: real and
    P :: \<open>'b \<Rightarrow> bool\<close>
  assumes
    \<open>\<And> x. \<turnstile>spmf \<lbrace>P\<rbrace> f x \<lbrace>P\<rbrace>\<close>
    \<open>\<And> x val. P val \<Longrightarrow> prob_fail (f x val) \<le> p\<close>
    \<open>P val\<close>
  shows
    \<open>prob_fail (foldM_spmf f xs val) \<le> length xs * p\<close>
    (is \<open>?L xs val \<le> _\<close>)
using assms proof (induction xs arbitrary: val)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)

  note assms = \<open>P val\<close> assms

  let ?val' = \<open>f x val\<close>
  let ?\<mu>' = \<open>measure_spmf ?val'\<close>

  have
    \<open>?L (x # xs) val =
      prob_fail ?val' + \<integral> val'. prob_fail (foldM_spmf f xs val') \<partial> ?\<mu>'\<close>
    (is \<open>_ = _ + \<integral> val'. ?prob_fail val' \<partial> _\<close>)
    by (simp add: pmf_bind_spmf_None)

  also have \<open>\<dots> \<le> p + \<integral> _. length xs * p \<partial> ?\<mu>'\<close>
  proof (rule add_mono)
    from assms show \<open>prob_fail ?val' \<le> p\<close> by simp

    from Cons.IH assms
    show \<open>(\<integral> val'. ?prob_fail val' \<partial> ?\<mu>') \<le> \<integral> _. length xs * p \<partial> ?\<mu>'\<close>
      apply (intro integral_mono_AE)
      by (simp_all add:
        integrable_prob_fail_foldM_spmf Utils_SPMF_Hoare.hoare_triple_def)
  qed

  also from assms have \<open>\<dots> \<le> p + length xs * p\<close>
    apply simp
    by (meson landau_omega.R_trans mult_left_le_one_le of_nat_0_le_iff pmf_nonneg weight_spmf_le_1 weight_spmf_nonneg zero_le_mult_iff)

  finally show ?case by (simp add: algebra_simps)
qed

lemma lossless_foldM_spmf :
  assumes
    \<open>\<And> x. \<turnstile>spmf \<lbrace>P\<rbrace> f x \<lbrace>P\<rbrace>\<close>
    \<open>\<And> x val. P val \<Longrightarrow> lossless_spmf (f x val)\<close>
    \<open>P val\<close>
  shows \<open>lossless_spmf <| foldM_spmf f xs val\<close>
  using assms prob_fail_foldM_spmf_le[of P f 0]
  by (simp add: lossless_iff_pmf_None)

lemma lossless_foldM_spmf' [simp] :
  assumes \<open>\<And> x val. lossless_spmf <| f x val\<close>
  shows \<open>lossless_spmf <| foldM_spmf f xs val\<close>
  using assms
  by (auto intro!: lossless_foldM_spmf simp add: hoare_triple_def)

end