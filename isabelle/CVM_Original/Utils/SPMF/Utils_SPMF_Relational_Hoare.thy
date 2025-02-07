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
  show ?R if ?L using that by (auto elim!: rel_spmfE)

  let ?pq =
    \<open>pair_spmf (mk_lossless p) (mk_lossless q)
      |> scale_spmf (weight_spmf p)\<close>

  show ?L if ?R
  proof (rule rel_spmfI[of ?pq])
    from that show \<open>(x, y) \<in> set_spmf ?pq \<Longrightarrow> P x \<and> Q y\<close> for x y
      unfolding set_scale_spmf by (simp split: if_splits)

    from that mk_lossless_back_eq[of p] mk_lossless_back_eq[of q] show
      \<open>map_spmf fst ?pq = p\<close> \<open>map_spmf snd ?pq = q\<close>
      unfolding map_scale_spmf by (auto simp add: weight_mk_lossless)
  qed
qed

lemma rel_spmf_True_iff_weight_spmf_eq [simp] :
  \<open>rel_spmf \<lblot>\<lblot>True\<rblot>\<rblot> p q \<longleftrightarrow> weight_spmf p = weight_spmf q\<close>
  using rel_spmf_conj_iff_ae_measure_spmf_conj[of \<open>\<lblot>True\<rblot>\<close>] by auto

(*
This result says that if we know that the outputs of `p` and `p'` agree with
each other whenever they are executed by the same source of randomness, and
wherever `p` doesn't fail (ie `ord_spmf (=) p p'`),
then the probability that a successful output of `p` satisfies `P` is \<le> that of
`p'` (ie `p {x | P x} \<le> p' {x | P x}` by viewing the output distributions of
`p` and `p'` as measures restricted to their successful outputs).
*)
(* lemma prob_le_prob_of_ord_spmf_eq :
  fixes P p p'
  assumes \<open>p \<sqsubseteq> p'\<close>
  shows \<open>\<P>(\<omega> in measure_spmf p. P \<omega>) \<le> \<P>(\<omega> in measure_spmf p'. P \<omega>)\<close>
  using assms
  by (simp add: space_measure_spmf ord_spmf_eqD_measure) *)

lemma prob_fail_eq_of_rel_spmf :
  assumes \<open>rel_spmf R p p'\<close>
  shows \<open>prob_fail p = prob_fail p'\<close>
  using assms
  by (simp add: pmf_None_eq_weight_spmf rel_spmf_weightD)

abbreviation relational_hoare_triple
  (\<open>\<turnstile>spmf \<lbrace> _ \<rbrace> \<langle> _ | _ \<rangle> \<lbrace> _ \<rbrace>\<close> [21, 20, 20, 21] 60) where
  \<open>(\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>) \<equiv> (\<And> x x'. R x x' \<Longrightarrow> rel_spmf S (f x) (f' x'))\<close>

lemma postcond_true [simp] :
  \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrace> \<equiv> (
    \<And> x x'. R x x' \<Longrightarrow> weight_spmf (f x) = weight_spmf (f' x'))\<close>
  by (simp add: lossless_weight_spmfD)

lemma skip_left [simp] :
  assumes \<open>\<And> x. lossless_spmf (f' x)\<close>
  shows
    \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f >>> return_spmf | f'\<rangle> \<lbrace>S\<rbrace> \<equiv> (\<And> x. \<turnstile>spmf \<lbrace>R x\<rbrace> f' \<lbrace>S (f x)\<rbrace>)\<close>
  using assms
  by (simp add: rel_spmf_return_spmf1)

lemma skip_right [simp] :
  assumes \<open>\<And> x. lossless_spmf (f x)\<close>
  shows
    \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f' >>> return_spmf\<rangle> \<lbrace>S\<rbrace> \<equiv>
    (\<And> x'. \<turnstile>spmf \<lbrace>flip R x'\<rbrace> f \<lbrace>flip S (f' x')\<rbrace>)\<close>
  apply standard
  using assms
  by (simp_all add: rel_spmf_return_spmf2)

(* lemma seq :
  assumes
    \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>\<close>
    \<open>\<And> x x'. R x x' \<Longrightarrow> \<turnstile>spmf \<lbrace>S\<rbrace> \<langle>g x | g' x'\<rangle> \<lbrace>T\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>(\<lambda> x. (x |> (f >=> g x))) | (\<lambda> x. (x |> (f' >=> g' x)))\<rangle> \<lbrace>T\<rbrace>\<close>
  using assms by (blast intro: rel_spmf_bindI) *)

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

lemma loop_enumerate :
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

lemma loop :
  assumes \<open>\<And> idx x.
    \<turnstile>spmf \<lbrace>R' idx x\<rbrace> \<langle>f x | f' x\<rangle> \<lbrace>R (Suc idx)\<rbrace>\<close>
  shows \<open>\<turnstile>spmf
    \<lbrace>R offset\<rbrace>
    \<langle>foldM_spmf f xs | foldM_spmf f' xs\<rangle>
    \<lbrace>R (offset + length xs)\<rbrace>\<close>
  using assms loop_enumerate
  by (metis foldM_eq_foldM_enumerate prod.sel(2))

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f x | f' x\<rangle> \<lbrace>R\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>foldM_spmf f xs | foldM_spmf f' xs\<rangle> \<lbrace>R\<rbrace>\<close>
  using assms loop[where offset = 0 and R = \<open>\<lblot>R\<rblot>\<close>] by blast

(* lemma hoare_ord_option_iff_ord_spmf :
  \<open>\<turnstile>spmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>ord_option S\<rbrakk> \<equiv>
  (\<And> x x'. R x x' \<Longrightarrow> ord_spmf S (f x) (f' x'))\<close>
  by (simp add: Utils_PMF_Relational.relational_hoare_triple_def) *)

(* lemma prob_fail_le_of_relational_hoare_triple :
  assumes
    \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>ord_option (=)\<rbrakk>\<close>
    \<open>R x x'\<close>
  shows
    \<open>prob_fprob_Nprob_failrob_fail prob_Noneprob_fail
  using assms
  by (auto
    intro!: ord_spmf_eqD_pmf_None[where Y = \<open>{}\<close>] 
    simp add: hoare_ord_option_iff_ord_spmf chain_empty) *)

context ord_spmf_syntax
begin

lemma foldM_spmf_ord_spmf_eq_of_ord_spmf_eq :
  assumes \<open>\<And> x val. f x val \<sqsubseteq>\<^bsub>(=)\<^esub> f' x val\<close>
  shows \<open>foldM_spmf f xs val \<sqsubseteq>\<^bsub>(=)\<^esub> foldM_spmf f' xs val\<close>
proof -
  let ?go = \<open>\<lambda> f. case_option fail_spmf <<< f\<close>

  from assms have \<open>\<turnstile>pmf
    \<lbrakk>le_option\<rbrakk> \<langle>foldM_pmf (?go f) xs | foldM_pmf (?go f') xs\<rangle> \<lbrakk>le_option\<rbrakk>\<close>
    apply (intro Utils_PMF_Relational_Hoare.loop_unindexed)
    by (auto split: option.splits)

  then show ?thesis by (simp add: foldM_spmf_eq_foldM_pmf_case)
qed

lemma prob_measure_spmf_le_of_ord_spmf :
  assumes \<open>p \<sqsubseteq>\<^bsub>(=)\<^esub> q\<close>
  shows \<open>\<P>(x in measure_spmf p. P x) \<le> \<P>(y in measure_spmf q. P y)\<close>
  using assms by (simp add: ord_spmf_eqD_measure space_measure_spmf)

end

end