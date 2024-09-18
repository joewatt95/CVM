theory Utils_SPMF_Common

imports
  "HOL-Probability.SPMF"
  CVM.Utils_Function

begin

definition fail_spmf :: \<open>'a spmf\<close> where
  \<open>fail_spmf \<equiv> return_pmf None\<close>

definition prob_fail :: \<open>'a spmf \<Rightarrow> real\<close> where
  \<open>prob_fail \<equiv> flip pmf None\<close>

lemma prob_fail_or_pred_le_prob_fail_plus_prob :
  \<open>\<P>(x in measure_pmf p. x |> Option.case_option True P)
    \<le> prob_fail p + \<P>(x in measure_spmf p. P x)\<close>
proof -
  have \<open>{x. x |> Option.case_option True P} = {None} \<union> Some ` Collect P\<close>
    by (auto elim: case_optionE)

  then show ?thesis
    apply (simp add: prob_fail_def space_measure_spmf)
    using insert_def
    by (metis UNIV_I finite_measure.finite_measure_subadditive measure_measure_spmf_conv_measure_pmf measure_pmf.prob_space_axioms pmf.rep_eq prob_space_def sets_measure_pmf singleton_conv)
qed

(*
Here, `ord_spmf (R) p p'` says that:
If we view `p` and `p'` as modelling probabilistic programs, and evaluate them
together (ie parameterised over the same stream of random bits), and assuming
that `p` doesn't fail and evaluates to `x`, then:
  1. `p'` doesn't fail either and so evaluates to (say) `x'`
  2. `x R x'` holds

In brief, this allows us to compare the outputs of `p` and `p'` via `R`, modulo
the cases when `p` fails, ie doesn't terminate successfully.

With this, the Lemma below says that;
If we know that the outputs of `p` and `p'` agree with each other wherever `p`
doesn't fail (ie `ord_spmf (=) p p'`),
then the probability that a successful output of `p` satisfies `P` is \<le> that of `p'`
(ie `p {x | P x} \<le> p' {x | P x}` by viewing the output distributions of `p` and
`p'` as measures restricted to their successful outputs).
*)
lemma prob_le_prob_of_ord_spmf_eq :
  fixes P p p'
  assumes \<open>ord_spmf (=) p p'\<close>
  defines \<open>prob p'' \<equiv> \<P>(\<omega> in measure_spmf p''. P \<omega>)\<close>
  shows \<open>prob p \<le> prob p'\<close>

  using assms
  by (metis ennreal_le_iff measure_nonneg measure_spmf.emeasure_eq_measure ord_spmf_eqD_emeasure space_measure_spmf) 

definition kleisli_compose_left ::
  \<open>('a \<Rightarrow> 'b spmf) \<Rightarrow> ('b \<Rightarrow> 'c spmf) \<Rightarrow> 'a \<Rightarrow> 'c spmf\<close>
  (infixl \<open>>=>\<close> 50) where
  \<open>(f >=> g) \<equiv> \<lambda> x. bind_spmf (f x) g\<close>

definition kleisli_compose_right ::
  \<open>('b \<Rightarrow> 'c spmf) \<Rightarrow> ('a \<Rightarrow> 'b spmf) \<Rightarrow> 'a \<Rightarrow> 'c spmf\<close>
  (infixr \<open><=<\<close> 50) where
  \<open>(f <=< g) \<equiv> g >=> f\<close>

end