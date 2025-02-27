section \<open>spmf relational Hoare rules\<close>

theory Utils_SPMF_Relational_Hoare

imports
  ABY3_Protocols.Spmf_Common
  Utils_SPMF_FoldM_Hoare
  Utils_PMF_Relational_Hoare

begin

lemma rel_spmf_conj_iff_ae_measure_spmf_conj :
  \<open>rel_spmf (\<lambda> x y. P x \<and> Q y) p q \<longleftrightarrow> (
    (weight_spmf p = weight_spmf q) \<and>
    (AE x in measure_spmf p. P x) \<and>
    (AE y in measure_spmf q. Q y))\<close>
  (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof (rule iffI)
  show \<open>?L \<Longrightarrow> ?R\<close> by (fastforce elim: rel_spmfE)

  let ?pq =
    \<open>pair_spmf (mk_lossless p) (mk_lossless q)
      |> scale_spmf (weight_spmf p)\<close>

  show \<open>?R \<Longrightarrow> ?L\<close>
  proof (rule rel_spmfI[of ?pq])
    assume \<open>?R\<close>

    then show \<open>(x, y) \<in> set_spmf ?pq \<Longrightarrow> P x \<and> Q y\<close> for x y
      unfolding set_scale_spmf by (simp split: if_splits)

    from \<open>?R\<close> mk_lossless_back_eq[of p] mk_lossless_back_eq[of q]
    show \<open>map_spmf fst ?pq = p\<close> \<open>map_spmf snd ?pq = q\<close>
      unfolding map_scale_spmf by (auto simp add: weight_mk_lossless)
  qed
qed

lemma rel_spmf_True_iff_weight_spmf_eq [simp] :
  \<open>rel_spmf \<lblot>\<lblot>True\<rblot>\<rblot> p q \<longleftrightarrow> weight_spmf p = weight_spmf q\<close>
  using rel_spmf_conj_iff_ae_measure_spmf_conj[of \<open>\<lblot>True\<rblot>\<close>] by auto

lemma prob_fail_eq_of_rel_spmf :
  assumes \<open>rel_spmf R p p'\<close>
  shows \<open>prob_fail p = prob_fail p'\<close>
  using assms by (simp add: pmf_None_eq_weight_spmf rel_spmf_weightD)

subsection \<open>Relational Hoare triple over Kleisli morphism\<close>

abbreviation rel_hoare_triple
  (\<open>\<turnstile>spmf \<lbrace> _ \<rbrace> \<langle> _ | _ \<rangle> \<lbrace> _ \<rbrace>\<close> [21, 20, 20, 21] 60) where
  \<open>(\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>) \<equiv> (\<And> x x'. R x x' \<Longrightarrow> rel_spmf S (f x) (f' x'))\<close>

subsection \<open>Hoare rule for trivial postcondition\<close>

lemma rel_hoare_postcond_true [simp] :
  \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrace> \<equiv> (
    \<And> x x'. R x x' \<Longrightarrow> weight_spmf (f x) = weight_spmf (f' x'))\<close>
  by (simp add: lossless_weight_spmfD)

subsection \<open>One-sided Hoare skip rules\<close>

lemma rel_hoare_skip_left [simp] :
  assumes \<open>\<And> x. lossless_spmf (f' x)\<close>
  shows
    \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f >>> return_spmf | f'\<rangle> \<lbrace>S\<rbrace> \<equiv> (\<And> x. \<turnstile>spmf \<lbrace>R x\<rbrace> f' \<lbrace>S (f x)\<rbrace>)\<close>
  using assms by (simp add: rel_spmf_return_spmf1)

lemma rel_hoare_skip_right [simp] :
  assumes \<open>\<And> x. lossless_spmf (f x)\<close>
  shows
    \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f' >>> return_spmf\<rangle> \<lbrace>S\<rbrace> \<equiv>
    (\<And> x'. \<turnstile>spmf \<lbrace>flip R x'\<rbrace> f \<lbrace>flip S (f' x')\<rbrace>)\<close>
  apply standard using assms by (simp_all add: rel_spmf_return_spmf2)

subsection \<open>Two-sided Hoare rules for monadic fold\<close>

context
  fixes
    R :: \<open>nat \<Rightarrow> 'b \<Rightarrow>'c \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

private abbreviation (input)
  \<open>foldM_enumerate' \<equiv> \<lambda> f. foldM_spmf_enumerate f xs offset\<close>

private abbreviation (input)
  \<open>R' \<equiv> \<lambda> idx x val val'.
    (idx, x) \<in> set (List.enumerate offset xs) \<and>
    R idx val val'\<close>

lemma rel_hoare_foldM_enumerate :
  assumes \<open>\<And> idx x.
    \<turnstile>spmf \<lbrace>R' idx x\<rbrace> \<langle>f (idx, x) | f' (idx, x)\<rangle> \<lbrace>R (Suc idx)\<rbrace>\<close>
  shows \<open>\<turnstile>spmf
    \<lbrace>R offset\<rbrace>
    \<langle>foldM_enumerate' f | foldM_enumerate' f'\<rangle>
    \<lbrace>R (offset + length xs)\<rbrace>\<close>
using assms proof (induction xs arbitrary: offset)
  case Nil
  then show ?case by (simp add: foldM_enumerate_def)
next
  case (Cons _ _)
  then show ?case
    apply (simp flip: add_Suc add: foldM_enumerate_def)
    by (blast intro: rel_spmf_bindI)
qed

lemma rel_hoare_foldM_indexed' :
  assumes \<open>\<And> idx x.
    \<turnstile>spmf \<lbrace>R' idx x\<rbrace> \<langle>f x | f' x\<rangle> \<lbrace>R (Suc idx)\<rbrace>\<close>
  shows \<open>\<turnstile>spmf
    \<lbrace>R offset\<rbrace>
    \<langle>foldM_spmf f xs | foldM_spmf f' xs\<rangle>
    \<lbrace>R (offset + length xs)\<rbrace>\<close>
  using assms rel_hoare_foldM_enumerate
  by (metis foldM_eq_foldM_enumerate prod.sel(2))

end

lemmas rel_hoare_foldM_indexed = rel_hoare_foldM_indexed'[where offset = 0, simplified]

lemma rel_hoare_foldM :
  assumes \<open>\<And> x. \<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f x | f' x\<rangle> \<lbrace>R\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>foldM_spmf f xs | foldM_spmf f' xs\<rangle> \<lbrace>R\<rbrace>\<close>
  using assms rel_hoare_foldM_indexed[where R = \<open>\<lblot>R\<rblot>\<close>] by blast

subsection \<open>Helper lemmas for the CCPO ordering on SPMF\<close>

context ord_spmf_syntax
begin

text \<open>Hoare proof rule for the ordering between monadic folds, derived from
  relational Hoare rule for monadic folds over PMF.\<close>

lemma \<open>(\<And> x x'. R x x' \<Longrightarrow> f x \<sqsubseteq>\<^bsub>(=)\<^esub> f' x') \<equiv> (\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>le_option\<rbrakk>)\<close> .

lemma foldM_spmf_ord_spmf_eq_of_ord_spmf_eq :
  assumes \<open>\<And> x val. f x val \<sqsubseteq>\<^bsub>(=)\<^esub> f' x val\<close>
  shows \<open>foldM_spmf f xs val \<sqsubseteq>\<^bsub>(=)\<^esub> foldM_spmf f' xs val\<close>
proof -
  let ?go = \<open>\<lambda> f. case_option fail_spmf <<< f\<close>

  from assms have \<open>foldM_pmf (?go f) x val \<sqsubseteq>\<^bsub>(=)\<^esub> foldM_pmf (?go f') x val'\<close>
    if \<open>le_option val val'\<close> for x val val'
    apply (intro Utils_PMF_Relational_Hoare.rel_hoare_foldM)
      using that by (auto split: option.splits)

  then show ?thesis by (simp add: foldM_spmf_eq_foldM_pmf_case)
qed

lemma prob_measure_spmf_le_of_ord_spmf :
  assumes \<open>p \<sqsubseteq>\<^bsub>(=)\<^esub> q\<close>
  shows \<open>\<P>(x in measure_spmf p. P x) \<le> \<P>(y in measure_spmf q. P y)\<close>
  using assms by (simp add: ord_spmf_eqD_measure space_measure_spmf)

end

end