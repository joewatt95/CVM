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

abbreviation hoare_triple
  (\<open>\<turnstile>spmf \<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> (\<And> x. P x \<Longrightarrow> AE y in measure_spmf <| f x. Q y)\<close>

abbreviation hoare_triple_total
  (\<open>\<turnstile>spmf \<lbrakk> _ \<rbrakk> _ \<lbrakk> _ \<rbrakk>\<close> [21, 20, 21] 60) where
  \<open>\<turnstile>spmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<equiv> \<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>is_Some_and_pred Q\<rbrakk>\<close>

lemma hoare_triple_altdef :
  \<open>(\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<equiv> (\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>is_None_or_pred Q\<rbrakk>)\<close>
  apply standard
  using AE_measure_spmf_iff_AE_measure_pmf by blast+

lemma skip [simp] :
  \<open>(\<turnstile>spmf \<lbrace>P\<rbrace> return_spmf \<lbrace>Q\<rbrace>) \<equiv> (\<And> x. P x \<Longrightarrow> Q x)\<close>
  \<open>(\<turnstile>spmf \<lbrace>P\<rbrace> (\<lambda> x. return_spmf (f x)) \<lbrace>Q\<rbrace>) \<equiv> (\<And> x. P x \<Longrightarrow> Q (f x))\<close>
  apply standard
  by simp_all

(* lemma seq :
  assumes
    \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
    \<open>\<And> x. P x \<Longrightarrow> \<turnstile>spmf \<lbrace>Q\<rbrace> g x \<lbrace>R\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> (\<lambda> x. (x |> (f >=> g x))) \<lbrace>R\<rbrace>\<close>
  by (metis (mono_tags, lifting) AE_measure_spmf_iff UN_E assms(1,2) bind_UNION o_apply set_bind_spmf) *)

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
  assumes \<open>\<And> index x. \<turnstile>spmf \<lbrace>P' index x\<rbrace> f (index, x) \<lbrace>P (Suc index)\<rbrace>\<close>
  shows \<open>\<turnstile>spmf
    \<lbrace>P offset\<rbrace>
    foldM_spmf_enumerate f xs offset
    \<lbrace>P (offset + length xs)\<rbrace>\<close>
using assms proof (induction xs arbitrary: offset)
  case Nil
  then show ?case by (simp add: foldM_enumerate_def)
next
  case (Cons _ _)
  then show ?case
    apply (simp add: set_bind_spmf comp_def foldM_enumerate_def)
    by (metis (no_types, lifting) UN_E add_Suc member_bind)
qed

lemma loop :
  assumes \<open>\<And> index x. \<turnstile>spmf \<lbrace>P' index x\<rbrace> f x \<lbrace>P (Suc index)\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P offset\<rbrace> foldM_spmf f xs \<lbrace>P (offset + length xs)\<rbrace>\<close>
  using assms loop_enumerate
  by (metis foldM_eq_foldM_enumerate prod.sel(2))

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile>spmf \<lbrace>P\<rbrace> f x \<lbrace>P\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> foldM_spmf f xs \<lbrace>P\<rbrace>\<close>
  using assms loop[where offset = 0 and P = \<open>\<lblot>P\<rblot>\<close>] by blast

lemma
  assumes \<open>\<turnstile>spmf \<lbrace>(\<lambda> x. guard x \<and> P x)\<rbrace> body \<lbrace>P\<rbrace>\<close>
  shows
    while : \<open>\<turnstile>spmf \<lbrace>P\<rbrace> loop_spmf.while guard body \<lbrace>(\<lambda> x. \<not> guard x \<and> P x)\<rbrace>\<close> and
    while' : \<open>\<turnstile>spmf \<lbrace>P\<rbrace> loop_spmf.while guard body \<lbrace>P\<rbrace>\<close>
proof -
  show \<open>\<turnstile>spmf \<lbrace>P\<rbrace> loop_spmf.while guard body \<lbrace>(\<lambda> x. \<not> guard x \<and> P x)\<rbrace>\<close>
  proof (induction rule: loop_spmf.while_fixp_induct)
    (* Transfinite ordinal. *)
    case 1 show ?case by simp
  next
    (* Initial ordinal. *)
    case 2 show ?case by simp 
  next
    (* Successor ordinal. *)
    case 3
    with assms show ?case
      by (smt (z3) AE_measure_spmf_iff UN_E bind_UNION o_apply set_bind_spmf set_return_spmf singletonD)
  qed

  then show \<open>\<turnstile>spmf \<lbrace>P\<rbrace> loop_spmf.while guard body \<lbrace>P\<rbrace>\<close> by simp
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
      by (simp_all add: integrable_prob_fail_foldM_spmf)
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
  by (metis AE_measure_spmf_iff lossless_foldM_spmf)

end