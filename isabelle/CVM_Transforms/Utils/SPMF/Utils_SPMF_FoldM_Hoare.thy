subsection \<open>foldM\_spmf and related Hoare rules\<close>

theory Utils_SPMF_FoldM_Hoare

imports
  Probabilistic_While.While_SPMF
  Utils_PMF_FoldM_Hoare
  Utils_SPMF_Basic

begin

subsubsection \<open>foldM\_spmf\<close>

abbreviation foldM_spmf ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b spmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close> where
  \<open>foldM_spmf \<equiv> foldM bind_spmf return_spmf\<close>

abbreviation
  \<open>foldM_spmf_enumerate \<equiv> foldM_enumerate bind_spmf return_spmf\<close>

lemma foldM_spmf_eq_foldM_pmf_case :
  \<open>foldM_spmf f xs = foldM_pmf (case_option fail_spmf <<< f) xs <<< Some\<close>
  (is \<open>_ = Some >>> ?foldM_pmf\<close>)
proof -
  have \<open>?foldM_pmf = case_option fail_spmf (foldM_spmf f xs)\<close>
  proof (induction xs)
    case Nil
    then show ?case
      by (metis bind_return_pmf foldM.simps(1) try_spmf_def try_spmf_return_pmf_None2)
  next
    case (Cons _ _)
    then show ?case
      apply (intro ext)
      apply (simp split: option.splits)
      by (simp add: bind_return_pmf bind_spmf_def)
  qed

  then show ?thesis by simp 
qed

lemma foldM_spmf_of_pmf_eq :
  \<open>foldM_spmf (\<lambda> x. spmf_of_pmf <<< f x) xs = spmf_of_pmf <<< foldM_pmf f xs\<close>
  (is ?thesis_0)
  \<open>foldM_spmf (\<lambda> x. spmf_of_pmf <<< f x) xs val = spmf_of_pmf (foldM_pmf f xs val)\<close>
  (is ?thesis_1)
proof -
  show ?thesis_0
    apply (induction xs) by (simp_all add: spmf_of_pmf_bind)
  then show ?thesis_1 by simp
qed

lemma pmf_foldM_spmf_nil :
  \<open>pmf (foldM_spmf f [] val) val' = of_bool (Some val = val')\<close>
  by simp

lemma pmf_foldM_spmf_cons :
  \<open>pmf (foldM_spmf f (x # xs) val) y =
    measure_pmf.expectation (f x val) (
      \<lambda> val'. case val' of
        None \<Rightarrow> of_bool (y = None) |
        Some val' \<Rightarrow> pmf (foldM_spmf f xs val') y)\<close>
  unfolding foldM.simps bind_spmf_def pmf_bind
  by (auto
    intro: integral_cong_AE split: option.splits
    simp add: AE_measure_pmf_iff)

subsubsection \<open>Hoare triples for Kleisli morphisms over SPMF\<close>

text \<open>Hoare triple for partial correctness\<close>

abbreviation spmf_hoare_triple
  (\<open>\<turnstile>spmf \<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> (\<And> x. P x \<Longrightarrow> AE y in measure_spmf <| f x. Q y)\<close>

text \<open>Hoare triple for total correctness\<close>

abbreviation spmf_hoare_triple_total
  (\<open>\<turnstile>spmf \<lbrakk> _ \<rbrakk> _ \<lbrakk> _ \<rbrakk>\<close> [21, 20, 21] 60) where
  \<open>\<turnstile>spmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<equiv> \<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>is_Some_and_pred Q\<rbrakk>\<close>

lemma spmf_hoare_triple_altdef :
  \<open>(\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<equiv> (\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>is_None_or_pred Q\<rbrakk>)\<close>
  apply standard using AE_measure_spmf_iff_AE_measure_pmf by blast+

subsubsection \<open>Hoare rules for foldM\_spmf and while loops\<close>

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

lemma spmf_hoare_foldM_enumerate :
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

lemma spmf_hoare_foldM_indexed' :
  assumes \<open>\<And> idx x. \<turnstile>spmf \<lbrace>P' idx x\<rbrace> f x \<lbrace>P (Suc idx)\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P offset\<rbrace> foldM_spmf f xs \<lbrace>P (offset + length xs)\<rbrace>\<close>
  using assms spmf_hoare_foldM_enumerate
  by (metis foldM_eq_foldM_enumerate prod.sel(2))

end

lemmas spmf_hoare_foldM_indexed =
  spmf_hoare_foldM_indexed'[where offset = 0, simplified add_0]

lemma spmf_hoare_foldM :
  assumes \<open>\<And> x. \<turnstile>spmf \<lbrace>P\<rbrace> f x \<lbrace>P\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> foldM_spmf f xs \<lbrace>P\<rbrace>\<close>
  using assms spmf_hoare_foldM_indexed[where P = \<open>\<lblot>P\<rblot>\<close>] by blast

text
  \<open>Soundness proof of the Hoare while rule w.r.t. its denotational semantics,
  by induction on the transfinite fixpoint iteration sequence.\<close>

lemma (in loop_spmf) spmf_hoare_while :
  assumes \<open>\<turnstile>spmf \<lbrace>(\<lambda> x. guard x \<and> P x)\<rbrace> body \<lbrace>P\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> while \<lbrace>(\<lambda> x. \<not> guard x \<and> P x)\<rbrace>\<close>
proof (induction rule: while_fixp_induct)
  text \<open>Initial ordinal\<close>
  case bottom show ?case by simp
next
  text \<open>Successor ordinal\<close>
  case (step _)
  with assms show ?case
    by (smt (z3) AE_measure_spmf_iff UN_E bind_UNION o_apply set_bind_spmf set_return_spmf singletonD)
next
  text \<open>Transfinite ordinal\<close>
  case adm show ?case by simp
qed

subsubsection \<open>Other results about foldM\_spmf\<close>

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
    apply (intro add_mono integral_mono_AE) by simp_all

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