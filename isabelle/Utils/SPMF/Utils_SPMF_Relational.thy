theory Utils_SPMF_Relational

imports
  CVM.Utils_SPMF_FoldM

begin

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

lemma foldM_spmf_ord_spmf_eq_of_ord_spmf_eq :
  assumes \<open>\<And> x val. ord_spmf (=) (f x val) (f' x val)\<close>
  shows \<open>ord_spmf (=) (foldM_spmf f xs val) <| foldM_spmf f' xs val\<close>
  apply (induction xs arbitrary: val)
  using assms by (auto intro: ord_spmf_bindI)

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

lemma precond_false :
  \<open>\<turnstile>spmf \<lbrace>\<lblot>\<lblot>False\<rblot>\<rblot>\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>\<close>
  by (simp add: relational_hoare_triple_def)

lemma postcond_weaken :
  assumes
    \<open>\<And> x x'. S' x x' \<Longrightarrow> S x x'\<close>
    \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S'\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>f | f'\<rangle> \<lbrace>S\<rbrace>\<close>
  by (metis assms(1,2) rel_spmf_mono relational_hoare_triple_def)

lemma skip [simp] :
  \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>return_spmf | return_spmf\<rangle> \<lbrace>S\<rbrace>
  \<longleftrightarrow> (\<forall> x x'. R x x' \<longrightarrow> S x x')\<close>
  by (simp add: relational_hoare_triple_def) 

lemma skip' [simp] :
  \<open>\<turnstile>spmf \<lbrace>R\<rbrace> \<langle>(\<lambda> x. return_spmf (f x)) | (\<lambda> x. return_spmf (f' x))\<rangle> \<lbrace>S\<rbrace>
  \<longleftrightarrow> (\<forall> x x'. R x x' \<longrightarrow> S (f x) (f' x'))\<close>
  by (simp add: relational_hoare_triple_def)

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

abbreviation (input)
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

end