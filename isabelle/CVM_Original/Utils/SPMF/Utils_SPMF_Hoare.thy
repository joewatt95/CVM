theory Utils_SPMF_Hoare

imports
  Probabilistic_While.While_SPMF
  Utils_SPMF_FoldM
  Utils_PMF_Hoare

begin

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

(* lemma skip [simp] :
  \<open>(\<turnstile>spmf \<lbrace>P\<rbrace> return_spmf \<lbrace>Q\<rbrace>) \<equiv> (\<And> x. P x \<Longrightarrow> Q x)\<close>
  \<open>(\<turnstile>spmf \<lbrace>P\<rbrace> (\<lambda> x. return_spmf (f x)) \<lbrace>Q\<rbrace>) \<equiv> (\<And> x. P x \<Longrightarrow> Q (f x))\<close>
  by simp_all *)

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
  \<open>P' \<equiv> \<lambda> idx x val.
    (idx, x) \<in> set (List.enumerate offset xs) \<and>
    P idx val\<close>

lemma loop_enumerate :
  assumes \<open>\<And> idx x. \<turnstile>spmf \<lbrace>P' idx x\<rbrace> f (idx, x) \<lbrace>P (Suc idx)\<rbrace>\<close>
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
  assumes \<open>\<And> idx x. \<turnstile>spmf \<lbrace>P' idx x\<rbrace> f x \<lbrace>P (Suc idx)\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P offset\<rbrace> foldM_spmf f xs \<lbrace>P (offset + length xs)\<rbrace>\<close>
  using assms loop_enumerate
  by (metis foldM_eq_foldM_enumerate prod.sel(2))

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile>spmf \<lbrace>P\<rbrace> f x \<lbrace>P\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> foldM_spmf f xs \<lbrace>P\<rbrace>\<close>
  using assms loop[where offset = 0 and P = \<open>\<lblot>P\<rblot>\<close>] by blast

lemma (in loop_spmf) while :
  assumes \<open>\<turnstile>spmf \<lbrace>(\<lambda> x. guard x \<and> P x)\<rbrace> body \<lbrace>P\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> while \<lbrace>(\<lambda> x. \<not> guard x \<and> P x)\<rbrace>\<close>
proof (induction rule: while_fixp_induct)
  (* Initial ordinal. *)
  case bottom show ?case by simp
next
  (* Successor ordinal. *)
  case (step _)
  with assms show ?case
    by (smt (z3) AE_measure_spmf_iff UN_E bind_UNION o_apply set_bind_spmf set_return_spmf singletonD)
next
  (* Transfinite ordinal. *)
  case adm show ?case by simp
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
    \<open>prob_fail (foldM_spmf f xs val) \<le> length xs * p\<close> (is \<open>?L xs val \<le> _\<close>)
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

  also from assms Cons.IH
  have \<open>\<dots> \<le> p + \<integral> _. length xs * p \<partial> ?\<mu>'\<close>
    apply (intro add_mono integral_mono_AE)
    by simp_all

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