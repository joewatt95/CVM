theory Utils_SPMF_Rel

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
  - fails (ie returns false) when x is Some but x' is None
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

(* definition equiv_up_to_failure ::
  \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a spmf \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'b spmf \<Rightarrow> bool\<close>
  (\<open>\<turnstile> \<lbrakk> _ \<rbrakk> _ \<simeq> \<lbrakk> _ \<rbrakk> _\<close>) where
  \<open>\<turnstile> \<lbrakk> P \<rbrakk> p \<simeq> \<lbrakk> P' \<rbrakk> p' \<equiv> rel_spmf (\<lambda> x x'. P x \<longleftrightarrow> P' x') p p'\<close>

lemma equiv_up_to_failure_refl_intro :
  assumes \<open>p = p'\<close>
  shows \<open>\<turnstile> \<lbrakk>P\<rbrakk> p \<simeq> \<lbrakk>P\<rbrakk>p'\<close>

  by (simp add: assms equiv_up_to_failure_def rel_spmf_reflI)

lemma equiv_up_to_failure_symm :
  assumes \<open>\<turnstile> \<lbrakk>P\<rbrakk>p \<simeq> \<lbrakk>P'\<rbrakk>p'\<close>
  shows \<open>\<turnstile> \<lbrakk>P'\<rbrakk>p' \<simeq> \<lbrakk>P\<rbrakk>p\<close>

  using assms
  by (metis (mono_tags, lifting) conversep_iff equiv_up_to_failure_def option.rel_conversep pmf.rel_flip rel_spmf_mono_strong) 

lemma prob_le_fail_of_equiv :
  fixes p p' P P'
  assumes \<open>\<turnstile> \<lbrakk>P\<rbrakk>p \<simeq> \<lbrakk>P'\<rbrakk>p'\<close>
  defines
    \<open>prob \<equiv> \<P>(x in measure_spmf p. P x)\<close> and
    \<open>prob' \<equiv> \<P>(x' in measure_spmf p'. P' x')\<close>
  shows
    \<open>prob \<le> prob' + prob_fail p\<close> and
    \<open>\<bar>prob - prob'\<bar> \<le> prob_fail p\<close>
proof -
  show \<open>prob \<le> prob' + prob_fail p\<close>
    by (smt (verit, best) Collect_cong UNIV_I assms(1) assms(3) ennreal_inj equiv_up_to_failure_def measure_le_0_iff measure_spmf.bounded_measure measure_spmf.emeasure_eq_measure mem_Collect_eq nn_integral_cong nn_integral_spmf prob_def prob_fail_def rel_spmf_measureD space_count_space space_measure_spmf weight_return_pmf_None weight_spmf_conv_pmf_None weight_spmf_le_1)

  then show \<open>\<bar>prob - prob'\<bar> \<le> prob_fail p\<close>
    using equiv_up_to_failure_symm
    by (smt (verit, best) Collect_cong UNIV_I assms(1) assms(3) ennreal_inj equiv_up_to_failure_def measure_nonneg measure_spmf.bounded_measure measure_spmf.emeasure_eq_measure mem_Collect_eq nn_integral_cong nn_integral_spmf prob_def rel_spmf_measureD space_count_space space_measure_spmf weight_return_pmf_None)
qed *)

end