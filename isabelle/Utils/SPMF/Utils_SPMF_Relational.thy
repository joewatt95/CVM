theory Utils_SPMF_Relational

imports
  ABY3_Protocols.Spmf_Common
  CVM.Utils_SPMF_Hoare
  CVM.Utils_PMF_Relational
  CVM.Utils_SPMF_FoldM

begin

lemma rel_spmf_True_iff_weight_spmf_eq [simp] :
  \<open>rel_spmf \<lblot>\<lblot>True\<rblot>\<rblot> p q \<longleftrightarrow> weight_spmf p = weight_spmf q\<close>
  using mk_lossless_back_eq[of p] mk_lossless_back_eq[of q]
  by (fastforce
    intro:
      rel_spmfI[of
        \<open>scale_spmf (weight_spmf p) <|
          pair_spmf (mk_lossless p) (mk_lossless q)\<close>]
    dest: rel_spmf_weightD
    simp add: map_scale_spmf weight_mk_lossless)

(*
Roughly,`ord_spmf (R) p p'` allows us to compare the outputs of `p` and `p'`
(viewed as probabilistic programs), operating over the same source of
randomness, via `R`, ignoring the cases when `p` fails, ie doesn't terminate
successfully.

More precisely, `ord_spmf (R) p p' = rel_pmf (ord_option R) p p'`, where:
- `rel_pmf` probabilistically couples `p` and `p'` (viewed as measures) together
  so we can analyse them relationally, via R, as if they were programs
  operating over the same source of randomness.

  This is also used in the fundamental Lemma for SPMFs and related forms that
  are found in crypto game hopping proofs, to bound the distance (in terms of
  the total variation metric, or equivalently an L1 metric as our distributions
  have countable support) between them (see Lemma 5.16 in [1] and 4.1.11 in [2]).

  It's also worth noting here that this coupling technique forms the foundation
  of relational probabilistic hoare logic (see chapter 5 of [1]).

- `ord_option R x x'`:
  - ignores (ie returns true) when x is None
  - fails (ie returns false) when x step_defis Some but x' is None
  -  compares `y R y'` when `x` is `Some y` and `x'` is `Some y'`

References:
[1] Foundations of Probabilistic Programming
    https://www.cambridge.org/core/books/foundations-of-probabilistic-programming/819623B1B5B33836476618AC0621F0EE
[2] Modern discrete probability
    https://people.math.wisc.edu/~roch/mdp/
*)

(*
This result says that if we know that the outputs of `p` and `p'` agree with
each other whenever they are executed by the same source of randomness, and
wherever `p` doesn't fail (ie `ord_spmf (=) p p'`),
then the probability that a successful output of `p` satisfies `P` is \<le> that of
`p'` (ie `p {x | P x} \<le> p' {x | P x}` by viewing the output distributions of
`p` and `p'` as measures restricted to their successful outputs).
*)
lemma prob_le_prob_of_ord_spmf_eq :
  fixes P p p'
  assumes \<open>ord_spmf (=) p p'\<close>
  defines \<open>prob p'' \<equiv> \<P>(\<omega> in measure_spmf p''. P \<omega>)\<close>
  shows \<open>prob p \<le> prob p'\<close>
  using assms
  by (metis ennreal_le_iff measure_nonneg measure_spmf.emeasure_eq_measure ord_spmf_eqD_emeasure space_measure_spmf) 

lemma prob_fail_eq_of_rel_spmf :
  assumes \<open>rel_spmf R p p'\<close>
  shows \<open>prob_fail p = prob_fail p'\<close>
  using assms
  by (simp add: pmf_None_eq_weight_spmf prob_fail_def rel_spmf_weightD)

definition relational_hoare_triple ::
  \<open>['a \<Rightarrow> 'b \<Rightarrow> bool, 'a \<Rightarrow> 'c spmf, 'b \<Rightarrow> 'd spmf, 'c \<Rightarrow> 'd \<Rightarrow> bool] \<Rightarrow> bool\<close>
  (\<open>\<turnstile>spmf \<lbrace> _ \<rbrace> \<langle> _ | _ \<rangle> \<lbrace> _ \<rbrace>\<close> [21, 20, 20, 21] 60) where
  \<open>(\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>) \<equiv> \<forall> x x'. R x x' \<longrightarrow> rel_spmf S (f x) (f' x')\<close>

lemma precond_strengthen :
  assumes
    \<open>\<And> x x'. R x x' \<Longrightarrow> R' x x'\<close>
    \<open>\<turnstile>spmf \<lbrace>R'\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>\<close>
  by (metis assms(1,2) relational_hoare_triple_def)

lemma precond_false [simp] :
  \<open>\<turnstile>spmf \<lbrace>\<lblot>\<lblot>False\<rblot>\<rblot>\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>\<close>
  by (simp add: relational_hoare_triple_def)

lemma postcond_weaken :
  assumes
    \<open>\<And> x x'. S' x x' \<Longrightarrow> S x x'\<close>
    \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S'\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>\<close>
  by (metis assms(1,2) rel_spmf_mono relational_hoare_triple_def)

lemma postcond_true [simp] :
  fixes R f f'
  defines [simp] :
    \<open>relational_hoare_triple_true \<equiv> \<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrace>\<close>
  shows
    \<open>relational_hoare_triple_true \<longleftrightarrow> (
      \<forall> x x'. R x x' \<longrightarrow> weight_spmf (f x) = weight_spmf (f' x'))\<close>
    \<open>\<lbrakk>\<And> x. lossless_spmf <| f x; \<And> x. lossless_spmf <| f' x\<rbrakk> \<Longrightarrow>
      relational_hoare_triple_true\<close>
  by (simp_all add: relational_hoare_triple_def lossless_weight_spmfD)

lemma refl_eq [simp] :
  \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>\<lblot>x\<rblot> | \<lblot>x\<rblot>\<rangle> \<lbrace>(=)\<rbrace>\<close>
  \<open>\<turnstile>spmf \<lbrace>(=)\<rbrace> \<langle>f | f\<rangle> \<lbrace>(=)\<rbrace>\<close>
  \<open>\<turnstile>spmf \<lbrace>(\<lambda> x x'. S x x' \<and> x = x')\<rbrace> \<langle>f | f\<rangle> \<lbrace>(=)\<rbrace>\<close>
  by (simp_all add: relational_hoare_triple_def spmf_rel_eq)

lemma skip [simp] :
  \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>return_spmf | return_spmf\<rangle> \<lbrace>S\<rbrace>
  \<longleftrightarrow> (\<forall> x x'. R x x' \<longrightarrow> S x x')\<close>
  by (simp add: relational_hoare_triple_def) 

lemma skip_left [simp] :
  assumes \<open>\<And> x. lossless_spmf (f x)\<close>
  shows
    \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>return_spmf | f\<rangle> \<lbrace>S\<rbrace>
    \<longleftrightarrow> (\<forall> x. \<turnstile>spmf \<lbrace>R x\<rbrace> f \<lbrace>S x\<rbrace>)\<close>
  using assms
  by (auto simp add: relational_hoare_triple_def Utils_SPMF_Hoare.hoare_triple_def SPMF.rel_spmf_return_spmf1)

lemma skip_right [simp] :
  assumes \<open>\<And> x. lossless_spmf (f x)\<close>
  shows
    \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | return_spmf\<rangle> \<lbrace>S\<rbrace>
    \<longleftrightarrow> (\<forall> x'. \<turnstile>spmf \<lbrace>flip R x'\<rbrace> f \<lbrace>flip S x'\<rbrace>)\<close>
  using assms
  by (auto simp add: relational_hoare_triple_def Utils_SPMF_Hoare.hoare_triple_def SPMF.rel_spmf_return_spmf2)

lemma skip' [simp] :
  \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>(\<lambda> x. return_spmf (f x)) | (\<lambda> x. return_spmf (f' x))\<rangle> \<lbrace>S\<rbrace>
  \<longleftrightarrow> (\<forall> x x'. R x x' \<longrightarrow> S (f x) (f' x'))\<close>
  by (simp add: relational_hoare_triple_def)

lemma skip_left' [simp] :
  assumes \<open>\<And> x. lossless_spmf (f' x)\<close>
  shows
    \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>(\<lambda> x. return_spmf (f x)) | f'\<rangle> \<lbrace>S\<rbrace>
    \<longleftrightarrow> (\<forall> x. \<turnstile>spmf \<lbrace>R x\<rbrace> f' \<lbrace>S (f x)\<rbrace>)\<close>
  using assms
  by (auto simp add: relational_hoare_triple_def Utils_SPMF_Hoare.hoare_triple_def SPMF.rel_spmf_return_spmf1)

lemma skip_right' [simp] :
  assumes \<open>\<And> x. lossless_spmf (f x)\<close>
  shows
    \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | (\<lambda> x. return_spmf (f' x))\<rangle> \<lbrace>S\<rbrace>
    \<longleftrightarrow> (\<forall> x'. \<turnstile>spmf \<lbrace>flip R x'\<rbrace> f \<lbrace>flip S (f' x')\<rbrace>)\<close>
  using assms
  by (auto simp add: relational_hoare_triple_def Utils_SPMF_Hoare.hoare_triple_def SPMF.rel_spmf_return_spmf2)

lemma if_then_else :
  assumes
    \<open>\<And> x x'. R x x' \<Longrightarrow> f x \<longleftrightarrow> f' x'\<close>
    \<open>\<turnstile>spmf \<lbrace>(\<lambda> x x'. f x \<and> R x x')\<rbrace> \<langle>g | g'\<rangle> \<lbrace>S\<rbrace>\<close>
    \<open>\<turnstile>spmf \<lbrace>(\<lambda> x x'. \<not> f x \<and> R x x')\<rbrace> \<langle>h | h'\<rangle> \<lbrace>S\<rbrace>\<close>
  shows \<open>\<turnstile>spmf
    \<lbrace>R\<rbrace>
    \<langle>(\<lambda> x. if f x then g x else h x) | (\<lambda> x. if f' x then g' x else h' x)\<rangle>
    \<lbrace>S\<rbrace>\<close>
  using assms by (simp add: relational_hoare_triple_def)

lemma seq :
  assumes
    \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>\<close>
    \<open>\<turnstile>spmf \<lbrace>S\<rbrace> \<langle>g | g'\<rangle> \<lbrace>T\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>(f >=> g) | (f' >=> g')\<rangle> \<lbrace>T\<rbrace>\<close>
  using assms
  by (auto
    intro!: rel_spmf_bindI
    simp add: relational_hoare_triple_def)

lemma seq' :
  assumes
    \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>\<close>
    \<open>\<And> x x'. R x x' \<Longrightarrow> \<turnstile>spmf \<lbrace>S\<rbrace> \<langle>g x | g' x'\<rangle> \<lbrace>T\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>(\<lambda> x. (x |> (f >=> g x))) | (\<lambda> x. (x |> (f' >=> g' x)))\<rangle> \<lbrace>T\<rbrace>\<close>
  using assms
  by (auto
    intro!: rel_spmf_bindI
    simp add: relational_hoare_triple_def)

context
  fixes
    R :: \<open>nat \<Rightarrow> 'b \<Rightarrow>'c \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

private abbreviation (input)
  \<open>foldM_enumerate' fn \<equiv> foldM_spmf_enumerate fn xs offset\<close>

private abbreviation (input)
  \<open>R' index x val val' \<equiv>
    (index, x) \<in> set (List.enumerate offset xs) \<and>
    R index val val'\<close>

lemma loop_enumerate :
  assumes \<open>\<And> index x.
    \<turnstile>spmf \<lbrace>R' index x\<rbrace> \<langle>f (index, x) | f' (index, x)\<rangle> \<lbrace>R (Suc index)\<rbrace>\<close>
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
    apply (simp add: foldM_enumerate_def)
    by (fastforce
      intro!: seq[where S = \<open>R <| Suc offset\<close>]
      simp add: relational_hoare_triple_def add_Suc[symmetric]
      simp del: add_Suc)
qed

lemma loop :
  assumes \<open>\<And> index x.
    \<turnstile>spmf \<lbrace>R' index x\<rbrace> \<langle>f x | f' x\<rangle> \<lbrace>R (Suc index)\<rbrace>\<close>
  shows \<open>\<turnstile>spmf
    \<lbrace>R offset\<rbrace>
    \<langle>foldM_spmf f xs | foldM_spmf f' xs\<rangle>
    \<lbrace>R (offset + length xs)\<rbrace>\<close>
  using assms
  by (auto
    intro: loop_enumerate
    simp add: foldM_eq_foldM_enumerate[where ?offset = offset])

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f x | f' x\<rangle> \<lbrace>R\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>foldM_spmf f xs | foldM_spmf f' xs\<rangle> \<lbrace>R\<rbrace>\<close>
  using loop[where ?R = \<open>\<lambda> _ x. R x\<close>, where ?offset = 0] assms
  by (fastforce simp add: relational_hoare_triple_def curry_def snd_def)

lemma hoare_ord_option_iff_ord_spmf :
  \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>ord_option S\<rbrakk>
  \<longleftrightarrow> (\<forall> x x'. R x x' \<longrightarrow> ord_spmf S (f x) (f' x'))\<close>
  by (simp add: Utils_PMF_Relational.relational_hoare_triple_def)

lemma prob_fail_le_of_relational_hoare_triple :
  assumes
    \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>ord_option (=)\<rbrakk>\<close>
    \<open>R x x'\<close>
  shows
    \<open>prob_fail (f' x') \<le> prob_fail (f x)\<close>
  using assms
  by (auto
    intro!: ord_spmf_eqD_pmf_None[where Y = \<open>{}\<close>] 
    simp add: hoare_ord_option_iff_ord_spmf  prob_fail_def chain_empty)

lemma foldM_spmf_ord_spmf_eq_of_ord_spmf_eq :
  assumes \<open>\<And> x val. ord_spmf (=) (f x val) (f' x val)\<close>
  shows \<open>ord_spmf (=) (foldM_spmf f xs val) (foldM_spmf f' xs val)\<close>
proof -
  let ?go = \<open>\<lambda> f x. case_option fail_spmf (f x)\<close>

  have \<open>\<turnstile>pmf
    \<lbrakk>ord_option (=)\<rbrakk>
    \<langle>foldM_pmf (?go f) xs | foldM_pmf (?go f') xs\<rangle>
    \<lbrakk>ord_option (=)\<rbrakk>\<close>
    by (fastforce
      intro: Utils_PMF_Relational.loop_unindexed
      simp add: assms hoare_ord_option_iff_ord_spmf fail_spmf_def
      split: option.splits)

  then show ?thesis
    by (simp add:
      foldM_spmf_eq_foldM_pmf_case
      Utils_PMF_Relational.relational_hoare_triple_def)
qed

text
  \<open>If 2 probabilistic if-then-else expressions differ in only one branch of
  computation, the total variation metric between their output distributions
  is bounded by the probability that their guard condition evaluates such that
  that branch of computation is taken.

  This generalises and captures the essence behind bounding the distance between
  running a while loop for only 1 iteration vs running it for \<ge> 1 iterations.

  The proof of this result utilises the fundamental lemma for spmfs, along with
  automation provided by our probabilistic relational Hoare logic for spmfs.

  Note that the lossless assumptions are there because the proof uses
  `pair_spmf` to "pair" the original function with a boolean flag indicating
  if the condition evaluated to true or not. This is in turned used alongside
  the fundamental lemma.\<close>
lemma measure_spmf_dist_ite_ite_le :
  fixes cond g and f f' :: \<open>'a \<Rightarrow> 'a spmf\<close>
  assumes [simp] :
    \<open>\<And> x. lossless_spmf <| f x\<close>
    \<open>\<And> x. lossless_spmf <| f' x\<close>
    \<open>\<And> x. lossless_spmf <| g x\<close>
  defines [simp] : \<open>go \<equiv> \<lambda> f x. if cond x then f x else g x\<close>
  shows
    \<open>\<bar>\<P>(x in measure_spmf <| p \<bind> go f. P x)
      - \<P>(x in measure_spmf <| p \<bind> go f'. P x)\<bar>
    \<le> \<P>(x in measure_spmf p. cond x)\<close>
    (is \<open>?L \<le> _\<close>)
proof -
  let ?kleisli_spmf_p = \<open>(>=>) \<lblot>p\<rblot>\<close>
  let ?go_with_flag = \<open>\<lambda> f x.
    if cond x
    then map_spmf (Pair True) (f x)
    else map_spmf (Pair False) (g x)\<close>

  note [simp] = space_measure_spmf

  have \<open>?L =
    \<bar>\<P>(x in measure_spmf <| p \<bind> ?go_with_flag f. P (snd x))
      - \<P>(x in measure_spmf <| p \<bind> ?go_with_flag f'. P (snd x))\<bar>\<close>
    apply (simp add:
      if_distrib map_spmf_bind_spmf comp_def
      measure_map_spmf[
        of snd, where A = \<open>Collect P\<close>,
        simplified vimage_def, simplified, symmetric])
    unfolding
      map_spmf_bind_spmf comp_def bind_map_spmf spmf.map_comp snd_conv
      spmf.map_ident ..

  also have \<open>\<dots> \<le> \<P>(x in measure_spmf <| p \<bind> ?go_with_flag f. fst x)\<close>
  proof -
    have \<open>\<turnstile>spmf
      \<lbrace>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrace>
      \<langle>?kleisli_spmf_p (?go_with_flag f) | ?kleisli_spmf_p (?go_with_flag f')\<rangle>
      \<lbrace>(\<lambda> (flag, y) (flag', y'). (flag \<longleftrightarrow> flag') \<and> (\<not> flag \<longrightarrow> y = y'))\<rbrace>\<close>
      unfolding SPMF.pair_spmf_return_spmf1[symmetric] pair_spmf_alt_def
      apply (subst bind_commute_spmf)
      apply (intro
        Utils_SPMF_Relational.seq'[where S = \<open>(=)\<close>]
        Utils_SPMF_Relational.if_then_else
        Utils_SPMF_Relational.seq'[where S = \<open>curry snd\<close>])
      by (auto intro: Utils_SPMF_Hoare.seq'[where Q = \<open>\<lblot>True\<rblot>\<close>])

    with SPMF.fundamental_lemma[
      where A = \<open>P <<< snd\<close>, where B = \<open>P <<< snd\<close>,
      where ?bad1.0 = fst, where ?bad2.0 = fst]
    show ?thesis
      by (fastforce
        intro: rel_spmf_mono
        simp add: Utils_SPMF_Relational.relational_hoare_triple_def)
  qed

  also have \<open>\<dots> \<le> \<P>(x in measure_spmf p. cond x)\<close>
  proof -
    have \<open>\<turnstile>spmf
      \<lbrace>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrace>
      \<langle>?kleisli_spmf_p (?go_with_flag f) | ?kleisli_spmf_p return_spmf\<rangle>
      \<lbrace>(\<lambda> (flag, _) x'. flag \<longleftrightarrow> cond x')\<rbrace>\<close>
      unfolding SPMF.pair_spmf_return_spmf1[symmetric] pair_spmf_alt_def
      by (fastforce intro:
        Utils_SPMF_Relational.seq[where S = \<open>(=)\<close>]
        Utils_SPMF_Hoare.if_then_else Utils_SPMF_Hoare.seq'[where Q = \<open>\<lblot>True\<rblot>\<close>])

    then show ?thesis
      by (auto
        dest: rel_spmf_measureD[where A = \<open>Collect fst\<close>]
        simp add: Utils_SPMF_Relational.relational_hoare_triple_def)
  qed

  finally show ?thesis .
qed

lemma measure_spmf_dist_ite_le :
  fixes cond and f g :: \<open>'a \<Rightarrow> 'a spmf\<close>
  assumes [simp] :
    \<open>\<And> x. lossless_spmf <| f x\<close>
    \<open>\<And> x. lossless_spmf <| g x\<close>
  shows
    \<open>\<bar>\<P>(x in measure_spmf <| do {x \<leftarrow> p; if cond x then f x else g x}. P x)
      - \<P>(x in measure_spmf <| p \<bind> g. P x)\<bar>
    \<le> \<P>(x in measure_spmf p. cond x)\<close>
  using measure_spmf_dist_ite_ite_le[where f' = g, where g = g] by simp

lemma measure_spmf_dist_ite_while_le :
  assumes [simp] :
    \<open>\<And> x. lossless_spmf <| body x\<close>
    \<open>\<And> x. lossless_spmf <| loop_spmf.while cond body x\<close>
  defines [simp] :
    \<open>while1 \<equiv> \<lambda> cond body x. if cond x then body x else return_spmf x\<close>
  shows
    \<open>\<bar>\<P>(x in measure_spmf <| p \<bind> while1 cond body. P x)
      - \<P>(x in measure_spmf <| p \<bind> loop_spmf.while cond body. P x)\<bar>
    \<le> \<P>(x in measure_spmf p. cond x)\<close>
  using measure_spmf_dist_ite_ite_le[
    where f' = \<open>body >=> loop_spmf.while cond body\<close>,
    where g = return_spmf, where cond = cond]
  by (simp add: loop_spmf.while.simps[symmetric])

lemma measure_spmf_dist_while_while_le :
  assumes [simp] :
    \<open>\<And> x. lossless_spmf <| body x\<close>
    \<open>\<And> x. lossless_spmf <| loop_spmf.while cond body x\<close>
    \<open>\<And> x. lossless_spmf <| body' x\<close>
    \<open>\<And> x. lossless_spmf <| loop_spmf.while cond body' x\<close>
  shows
    \<open>\<bar>\<P>(x in measure_spmf <| p \<bind> loop_spmf.while cond body. P x)
      - \<P>(x in measure_spmf <| p \<bind> loop_spmf.while cond body'. P x)\<bar>
    \<le> \<P>(x in measure_spmf p. cond x)\<close>
  using measure_spmf_dist_ite_ite_le[
    where f = \<open>body >=> loop_spmf.while cond body\<close>,
    where f' = \<open>body' >=> loop_spmf.while cond body'\<close>,
    where g = return_spmf, where cond = cond]
  by (simp add: loop_spmf.while.simps[symmetric])

thm SPMF.rel_spmf_bindI[
  THEN SPMF.fundamental_lemma]

lemma
  fixes h cond g xs val P
  assumes
    \<open>\<And> x val. \<P>(val in measure_spmf <| h x val. cond val) \<le> p\<close> and
    [simp] :
      \<open>\<And> val. lossless_spmf <| f val\<close>
      \<open>\<And> val. lossless_spmf <| f' val\<close>
      \<open>\<And> val. lossless_spmf <| g val\<close>
      \<open>\<And> x val. lossless_spmf <| h x val\<close>
  defines
    [simp] :
      \<open>foldM_spmf' \<equiv> \<lambda> f xs val.
        foldM_spmf (\<lambda> x val. bind_spmf (h x val) (\<lambda> val. if cond val then f val else g val)) xs val\<close> and
    [simp] : \<open>prob \<equiv> \<lambda> p. \<P>(x in measure_spmf p. P x)\<close>
  shows
    \<open>\<bar>prob (foldM_spmf' f xs val) - prob (foldM_spmf' f' xs val)\<bar> \<le> p * length xs\<close>
    (is \<open>?L \<le> _\<close>)
using assms proof - 
  note [simp] = space_measure_spmf

  (* let ?kleisli_spmf_p = \<open>(>=>) \<lblot>p\<rblot>\<close> *)

  let ?go_with_flag = \<open>\<lambda> f x (flag, val). do {
    val \<leftarrow> h x val;
    if cond val
    then map_spmf (Pair True) (f val)
    else map_spmf (Pair False) (g val) }\<close>

  let ?fold_with_flag = \<open>\<lambda> f. foldM_spmf (?go_with_flag f)\<close>

  have
    \<open>map_spmf snd (?fold_with_flag f xs (flag, val)) = foldM_spmf' f xs val\<close>
    for f flag val
    apply (induction xs arbitrary: flag val)
    by (auto
      intro!: bind_spmf_cong
      simp add: map_spmf_bind_spmf map_spmf_conv_bind_spmf)

  then have \<open>?L =
    \<bar>\<P>(flag_val in measure_spmf <| ?fold_with_flag f xs (False, val). P (snd flag_val))
      - \<P>(flag_val in measure_spmf <| ?fold_with_flag f' xs (False, val). P (snd flag_val))\<bar>\<close>
    apply (simp add:
      if_distrib if_distribR map_spmf_bind_spmf comp_def
      measure_map_spmf[
        of snd, where A = \<open>Collect P\<close>,
        simplified vimage_def, simplified, symmetric])
    unfolding map_spmf_bind_spmf comp_def bind_map_spmf .

  also have \<open>\<dots> \<le>
    \<P>(flag_val in measure_spmf <| ?fold_with_flag f xs (False, val). fst flag_val)\<close>
    (is \<open>_ \<le> ?L xs val\<close>)
  proof -
    let ?invariant = \<open>\<lambda> (flag, y) (flag', y').
      (flag \<longleftrightarrow> flag') \<and> (\<not> flag \<longrightarrow> y = y')\<close>

    have \<open>\<turnstile>spmf
      \<lbrace>?invariant\<rbrace>
      \<langle>?fold_with_flag f xs | ?fold_with_flag f' xs\<rangle>
      \<lbrace>?invariant\<rbrace>\<close>
      apply (simp add: case_prod_beta')
      apply (intro Utils_SPMF_Relational.loop[where offset = 0])
      apply (simp add: in_set_enumerate_eq)
      apply (intro Utils_SPMF_Relational.seq'[where S = \<open>(=)\<close>])
      apply (simp add: Utils_SPMF_Relational.relational_hoare_triple_def)
      sorry

    with SPMF.fundamental_lemma[
      where A = \<open>P <<< snd\<close>, where B = \<open>P <<< snd\<close>,
      where ?bad1.0 = fst, where ?bad2.0 = fst]
    show ?thesis
      by (fastforce
        intro: rel_spmf_mono
        simp add: Utils_SPMF_Relational.relational_hoare_triple_def)
  qed

  also have \<open>\<dots> \<le> p * length xs\<close> (is \<open>_ \<le> ?R\<close>)
  proof (induction xs arbitrary: val)
    case Nil
    then show ?case
      apply simp
      by (metis indicator_simps(2) measure_return_pmf measure_spmf_spmf_of_pmf mem_Collect_eq nle_le prod.sel(1) spmf_of_pmf_return_pmf)
  next
    case (Cons x xs)
    then show ?case
      unfolding spmf_map_pred_true_eq_prob[symmetric]
      apply (simp add:
        algebra_simps map_spmf_bind_spmf comp_def spmf_bind spmf_map vimage_def)
      thm pmf_bind_spmf_None
      sorry
  qed

  finally show ?thesis .
qed

context
  fixes bad_event :: \<open>'a \<Rightarrow> bool\<close>
begin

definition
  \<open>eq_up_to_bad \<equiv> \<lambda> val val'.
    (bad_event val \<longleftrightarrow> bad_event val') \<and> (\<not> bad_event val \<longrightarrow> val = val')\<close>

context
  fixes f f' :: \<open>'b \<Rightarrow> 'a \<Rightarrow> 'a spmf\<close>
  notes [simp] = case_prod_beta' space_measure_spmf
  assumes
    same_weight_spmf : \<open>\<And> x val val'.
      weight_spmf (f x val) = weight_spmf (f' x val')\<close> and
    preserves_eq_up_to_bad : \<open>\<And> x.
      \<turnstile>spmf \<lbrace>(=)\<rbrace> \<langle>f x | f' x\<rangle> \<lbrace>eq_up_to_bad\<rbrace>\<close>
begin

definition
  \<open>f_with_bad_flag \<equiv> \<lambda> f x (bad_flag, val). (
    f x val |> map_spmf (
      if bad_flag
      then Pair True
      else (\<lambda> val'. (bad_event val', val'))))\<close>

abbreviation \<open>foldM_spmf_with_bad_flag \<equiv> foldM_spmf <<< f_with_bad_flag\<close>

lemma foldM_spmf_eq_up_to_bad_invariant :
  defines
    \<open>eq_up_to_bad_with_flag \<equiv> \<lambda> (bad_flag, val) (bad_flag', val').
      (bad_flag = bad_flag') \<and> (\<not> bad_flag \<longrightarrow> val = val')\<close>
  shows \<open>\<turnstile>spmf
    \<lbrace>eq_up_to_bad_with_flag\<rbrace>
    \<langle>foldM_spmf_with_bad_flag f xs | foldM_spmf_with_bad_flag f' xs\<rangle>
    \<lbrace>eq_up_to_bad_with_flag\<rbrace>\<close>
proof -
  let ?precond = \<open>\<lambda> f flag_val flag'_val'.
    f (fst flag_val) \<and> eq_up_to_bad_with_flag flag_val flag'_val'\<close>

  let ?mk_branch = \<open>\<lambda> branch f x. snd >>> f x >>> map_spmf branch\<close> 
  let ?if_branch = \<open>?mk_branch <| Pair True\<close>
  let ?else_branch = \<open>?mk_branch <| \<lambda> val'. (bad_event val', val')\<close>

  note [simp] = assms f_with_bad_flag_def

  from same_weight_spmf have \<open>\<turnstile>spmf
    \<lbrace>?precond id\<rbrace>
    \<langle>?if_branch f x | ?if_branch f' x\<rangle>
    \<lbrace>eq_up_to_bad_with_flag\<rbrace>\<close> for x
    by (auto
      intro: seq[where S = \<open>\<lblot>\<lblot>True\<rblot>\<rblot>\<close>]
      simp add: map_spmf_conv_bind_spmf)

  moreover from preserves_eq_up_to_bad have \<open>\<turnstile>spmf
    \<lbrace>?precond Not\<rbrace>
    \<langle>?else_branch f x | ?else_branch f' x\<rangle>
    \<lbrace>eq_up_to_bad_with_flag\<rbrace>\<close> for x
    apply (simp add: map_spmf_conv_bind_spmf)
    apply (intro seq[where S = eq_up_to_bad])
    by (auto simp only:
      eq_up_to_bad_def skip' prod.sel relational_hoare_triple_def)

  ultimately show ?thesis
    by (fastforce
      intro: loop_unindexed if_then_else
      simp add: if_distrib if_distribR)
qed

lemma
  fixes xs bad_flag
  assumes \<open>\<not> bad_flag \<Longrightarrow> val = val'\<close>
  defines
    \<open>prob \<equiv> \<lambda> P f val.
      \<P>(flag_val in measure_spmf <| foldM_spmf f xs (bad_flag, val). P flag_val)\<close>
  shows
    \<open>\<bar>prob (P <<< snd) (f_with_bad_flag f) val
      - prob (P <<< snd) (f_with_bad_flag f') val'\<bar>
    \<le> prob fst (f_with_bad_flag f) val\<close>
  using assms foldM_spmf_eq_up_to_bad_invariant
  unfolding case_prod_beta 
  apply (simp add: relational_hoare_triple_def)
  apply (intro SPMF.fundamental_lemma[where ?bad2.0 = fst])
  by (smt (verit) rel_spmf_mono)

lemma
  fixes xs val
  assumes
    \<open>\<And> x val. \<P>(val in measure_spmf <| f x val. bad_event val) \<le> p\<close>
  defines [simp] :
    \<open>prob \<equiv> \<lambda> P f.
      \<P>(val in measure_spmf <| foldM_spmf f xs val. P val)\<close>
  shows
    \<open>\<bar>prob P f - prob P f'\<bar> \<le> real (length xs) * p\<close>
    (is \<open>?L \<le> ?R\<close>)
proof -
  let ?prob_with_flag = \<open>\<lambda> P f.
    \<P>(flag_val in measure_spmf <|
        foldM_spmf_with_bad_flag f xs (False, val).
      P flag_val)\<close>

  have
    \<open>map_spmf snd (foldM_spmf_with_bad_flag f xs (flag, val)) =
      foldM_spmf f xs val\<close> for f flag val
    apply (induction xs arbitrary: flag val)
    by (auto
      intro!: bind_spmf_cong
      simp add: f_with_bad_flag_def map_spmf_bind_spmf map_spmf_conv_bind_spmf)

  then have \<open>?L =
    \<bar>?prob_with_flag (P <<< snd) f - ?prob_with_flag (P <<< snd) f'\<bar>\<close>
    apply simp
    by (metis (no_types, lifting) measure_map_spmf vimage_Collect)

  also from assms(1) foldM_spmf_eq_up_to_bad_invariant
  have \<open>\<dots> \<le> ?prob_with_flag fst f\<close> (is \<open>_ \<le> ?L_0 False val\<close>)
    apply (simp add: eq_up_to_bad_def relational_hoare_triple_def)
    apply (intro SPMF.fundamental_lemma[where ?bad2.0 = fst])
    by (smt (verit) rel_spmf_mono)

  (* also have \<open>\<dots> = prob_fail (
    let go = \<lambda> x val. do {
      val \<leftarrow> f x val;
      if bad_event val then fail_spmf else return_spmf val }
    in foldM_spmf go xs val)\<close>
    (is \<open>_ = ?R_0 val\<close>)
  proof (induction xs)
    case Nil
    then show ?case
      by (simp add: prob_fail_def measure_return measure_spmf_return_spmf)
    next
      case (Cons x xs)
      then show ?case
        apply (simp add:
          prob_fail_def pmf_bind_spmf_None fail_spmf_def
          Let_def if_distrib if_distribR)
        unfolding
          fail_spmf_def return_bind_spmf return_None_bind_spmf
          pmf_return_pmf_1
        sorry
    qed *)

  also have \<open>\<dots> \<le> ?R\<close>
  proof (induction xs)
    case Nil
    then show ?case by (simp add: measure_return measure_spmf_return_spmf)
  next
    case (Cons x xs)
    then show ?case
      apply (simp
        add:
          f_with_bad_flag_def if_distrib if_distribR
          measure_spmf_bind comp_def algebra_simps)
      sorry
  qed

  finally show ?thesis .
qed

end

end

thm SPMF.fundamental_lemma[
  where p = \<open>foldM_spmf (\<lambda> x (flag, val). map_spmf (\<lambda> val'. (flag \<or> P val', val')) (f x val)) xs (flag, val)\<close>,
  where q = \<open>foldM_spmf (\<lambda> x (flag, val). map_spmf (\<lambda> val'. (flag \<or> P val', val')) (f' x val)) xs (flag', val)\<close>,
  where ?bad1.0 = fst, where ?bad2.0 = fst,
  where A = \<open>P <<< snd\<close>, where B = \<open>P <<< snd\<close>]

lemma
  assumes
    \<open>\<not> flag \<Longrightarrow> val = val'\<close>
    \<open>\<And> x val. rel_spmf (\<lambda> a b. (P a \<longleftrightarrow> P b) \<and> (\<not> P a \<longrightarrow> a = b)) (f x val) (f' x val)\<close>
  shows
    \<open>\<bar>Sigma_Algebra.measure (measure_spmf (foldM (\<bind>) return_spmf (\<lambda>x (flag, val). map_spmf (\<lambda>val'. (flag \<or> P val', val')) (f x val)) xs (flag, val))) {x. P (snd x)} -
      Sigma_Algebra.measure (measure_spmf (foldM (\<bind>) return_spmf (\<lambda>x (flag, val). map_spmf (\<lambda>val'. (flag \<or> P val', val')) (f' x val)) xs (flag, val'))) {y. P (snd y)}\<bar>
    \<le> Sigma_Algebra.measure (measure_spmf (foldM (\<bind>) return_spmf (\<lambda>x (flag, val). map_spmf (\<lambda>val'. (flag \<or> P val', val')) (f x val)) xs (flag, val))) {x. fst x}\<close>
  apply (intro SPMF.fundamental_lemma[of fst fst])
  using assms(1)
proof (induction xs arbitrary: flag val val')
  case Nil
  then show ?case
    by auto
next
  case (Cons x xs)
  show ?case
    apply (cases flag)

    subgoal
      apply simp
      apply (intro rel_spmf_bindI[where R = \<open>\<lambda> x y. fst x \<and> fst y\<close>])
      apply (simp add: spmf_rel_map)
      sorry

    subgoal
      using Cons(2)
      apply simp
      unfolding map_spmf_conv_bind_spmf bind_spmf_assoc
      apply (intro rel_spmf_bindI[OF assms(2)])
      subgoal for x y
        apply (intro rel_spmf_bindI[
          where R = \<open>\<lambda> xx yy. xx = (P x, x) \<and> yy = (P y, y)\<close>])
        apply simp
        apply (elim conjE)
        apply (simp add: case_prod_beta')
        apply (intro Cons(1)[simplified case_prod_beta' map_spmf_conv_bind_spmf])
        by auto
      done
    done
qed

(* Old, deprecated experiments below. *)

lemma
  fixes cond g
  assumes
    \<open>\<And> x. lossless_spmf (body x)\<close>
    \<open>\<And> x. lossless_spmf (loop_spmf.while cond body x)\<close>
  shows
    \<open>\<bar>\<P>(x in measure_spmf <| do {x \<leftarrow> p; if cond x then body x else return_spmf x}.
      P x)
      - \<P>(x in measure_spmf <| bind_pmf p <| loop_spmf.while cond body. P x)\<bar>
    \<le> \<P>(x in p. cond x)\<close>
    (is
      \<open>\<bar>\<P>(x in measure_spmf <| bind_pmf _ <| ?if. _)
        - ?prob (loop_spmf.while _ _)\<bar>
      \<le> ?R\<close>)
proof -
  let ?bind_spmf_p = \<open>(>=>) \<lblot>spmf_of_pmf p\<rblot>\<close>

  let ?if_with_flag = \<open>\<lambda> x. pair_spmf (?if x) (return_spmf <| cond x)\<close>

  let ?cond_with_flag = \<open>\<lambda> (x, _). cond x\<close>
  let ?body_with_flag = \<open>\<lambda> (x, _). pair_spmf (body x) (return_spmf True)\<close>
  let ?while_with_flag = \<open>\<lambda> flag x.
    loop_spmf.while ?cond_with_flag ?body_with_flag (x, flag)\<close>

  have while_with_flag_eq :
    \<open>?while_with_flag flag x = (
      if cond x
      then pair_spmf (loop_spmf.while cond body x) (return_spmf True)
      else return_spmf (x, flag))\<close> for flag x
    apply (auto simp add: loop_spmf.while_simps pair_spmf_alt_def)
    apply (intro bind_spmf_cong)
    apply blast

    (* To show that 2 while loops are equal, we appeal to their domain-theoretic
    denotational semantics as least fixed points of transfinite iteration
    sequences, and show, via transfinite induction, that they are upper bounds
    of each other's sequences.

    TODO: Try to derive a relational Hoare logic proof rule that provides a
    simpler API by abstracting away all this domain-theoretic fiddling.
    For reference, see ch5 of http://publications.rwth-aachen.de/record/814578/files/814578.pdf *)
    apply (intro spmf.leq_antisym)
    subgoal for x'
      apply (induction arbitrary: flag x x' rule: loop_spmf.while_fixp_induct[where guard = \<open>\<lambda> (x, _). cond x\<close>])
      by (auto
        intro!: ord_spmf_bind_reflI
        simp add: map_spmf_bind_spmf bind_map_spmf pair_spmf_alt_def loop_spmf.while_simps)

    subgoal for x'
      apply (induction arbitrary: flag x x' rule: loop_spmf.while_fixp_induct[where guard = cond])
      by (auto
        intro: ord_spmf_bind_reflI
        simp add: map_spmf_bind_spmf bind_map_spmf pair_spmf_alt_def loop_spmf.while_simps)
    done

  with assms have \<open>lossless_spmf (?while_with_flag flag x)\<close> for flag x
    by (simp add: pair_spmf_return_spmf2)

  then have \<open>\<turnstile>spmf
    \<lbrace>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrace>
    \<langle>?bind_spmf_p ?if_with_flag | ?bind_spmf_p (?while_with_flag False)\<rangle>
    \<lbrace>(\<lambda> (y, flag) (y', flag'). (flag \<longleftrightarrow> flag') \<and> (\<not> flag \<longrightarrow> y = y'))\<rbrace>\<close>
    apply (intro Utils_SPMF_Relational.seq'[where S = \<open>(=)\<close>])
    apply (simp add: Utils_SPMF_Relational.relational_hoare_triple_def spmf_rel_eq)
    unfolding pair_spmf_alt_def
    apply (simp add: if_distrib if_distribR loop_spmf.while.simps)
    apply (intro Utils_SPMF_Relational.if_then_else)
    apply blast
    apply (intro Utils_SPMF_Relational.seq'[where S = \<open>\<lambda> x (x', flag). flag\<close>])
    apply (simp add: Utils_SPMF_Relational.relational_hoare_triple_def)
    apply (metis (no_types, lifting) bind_return_spmf case_prodI option.rel_inject(2) rel_pmf_return_pmfI rel_spmf_bind_reflI)
    subgoal
      apply (subst Utils_SPMF_Relational.skip_left')
      apply (smt (verit, del_insts) case_prodE loop_spmf.while.simps lossless_return_spmf split_conv)
      by (auto
        intro!:
          Utils_SPMF_Hoare.while Utils_SPMF_Hoare.seq'
          Utils_SPMF_Hoare.postcond_true
        simp add: case_prod_beta')
    by (simp add: Utils_SPMF_Relational.relational_hoare_triple_def)

  with SPMF.fundamental_lemma[
    where p = \<open>p \<bind> ?if_with_flag\<close>,
    where q = \<open>p \<bind> (?while_with_flag False)\<close>,
    where A = \<open>P <<< fst\<close>, where B = \<open>P <<< fst\<close>,
    of snd snd]
  have
    \<open>\<bar>\<P>(x in measure_spmf <| p \<bind> ?if_with_flag. P (fst x))
      - \<P>(x in measure_spmf <| p \<bind> (?while_with_flag False). P (fst x))\<bar>
    \<le> \<P>(x in measure_spmf <| p \<bind> ?if_with_flag. snd x)\<close>
    by (fastforce
      intro: rel_spmf_mono
      simp add:
        Utils_SPMF_Relational.relational_hoare_triple_def space_measure_spmf)

  also have \<open>\<dots> \<le> ?R\<close>
  proof -
    from assms have \<open>\<turnstile>spmf
      \<lbrace>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrace>
      \<langle>?bind_spmf_p ?if_with_flag | ?bind_spmf_p return_spmf\<rangle>
      \<lbrace>(\<lambda> (_, flag) x'. flag \<longleftrightarrow> cond x')\<rbrace>\<close>
      unfolding pair_spmf_alt_def
      apply (intro Utils_SPMF_Relational.seq[where S = \<open>(=)\<close>])
      apply (simp add: Utils_SPMF_Relational.relational_hoare_triple_def spmf_rel_eq) 
      by (auto intro: Utils_SPMF_Hoare.seq' Utils_SPMF_Hoare.postcond_true)

    then show ?thesis
      by (auto
        dest: rel_spmf_measureD[where A = \<open>{x. snd x}\<close>]
        simp add: Utils_SPMF_Relational.relational_hoare_triple_def space_measure_spmf)
  qed

  finally show ?thesis
    apply (simp add: space_measure_spmf while_with_flag_eq)
    using measure_map_spmf[of fst, where A = \<open>{x. P x}\<close>, simplified vimage_def, simplified]
    by (smt (verit, best) bind_pmf_cong loop_spmf.while_simps(2) map_bind_pmf map_fst_pair_spmf pair_spmf_return_spmf scale_spmf_eq_same weight_return_spmf)
qed


end