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


definition kleisli_compose_left ::
  \<open>('a \<Rightarrow> 'b spmf) \<Rightarrow> ('b \<Rightarrow> 'c spmf) \<Rightarrow> 'a \<Rightarrow> 'c spmf\<close>
  (infixl \<open>>=>\<close> 50) where
  \<open>(f >=> g) \<equiv> \<lambda> x. bind_spmf (f x) g\<close>

definition kleisli_compose_right ::
  \<open>('b \<Rightarrow> 'c spmf) \<Rightarrow> ('a \<Rightarrow> 'b spmf) \<Rightarrow> 'a \<Rightarrow> 'c spmf\<close>
  (infixr \<open><=<\<close> 50) where
  \<open>(f <=< g) \<equiv> g >=> f\<close>

end