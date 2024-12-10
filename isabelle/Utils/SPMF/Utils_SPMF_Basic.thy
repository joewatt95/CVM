theory Utils_SPMF_Basic

imports
  "HOL-Probability.SPMF"
  CVM.Utils_Function

begin

definition fail_spmf :: \<open>'a spmf\<close> where
  \<open>fail_spmf \<equiv> return_pmf None\<close>

definition prob_fail :: \<open>'a spmf \<Rightarrow> real\<close> where
  \<open>prob_fail \<equiv> flip pmf None\<close>

lemma prob_fail_map_spmf_eq :
  \<open>prob_fail (map_spmf f p) = prob_fail p\<close>
  by (simp add: prob_fail_def pmf_None_eq_weight_spmf)

lemma spmf_map_pred_true_eq_prob :
  \<open>spmf (map_spmf P p) True = \<P>(x in measure_spmf p. P x)\<close>
  by (simp add: space_measure_spmf spmf_map vimage_def)

abbreviation fails_or_satisfies :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>fails_or_satisfies \<equiv> case_option True\<close>

abbreviation succeeds_and_satisfies :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>succeeds_and_satisfies \<equiv> case_option False\<close>

lemma prob_fails_or_satisfies_le_prob_fail_plus_prob :
  \<open>\<P>(x in measure_pmf p. x |> fails_or_satisfies P)
    \<le> prob_fail p + \<P>(x in measure_spmf p. P x)\<close>
proof -
  have \<open>Collect (fails_or_satisfies P) = {None} \<union> Some ` Collect P\<close>
    by (auto elim: case_optionE)

  then show ?thesis
    apply (simp add: prob_fail_def space_measure_spmf)
    using insert_def
    by (metis UNIV_I finite_measure.finite_measure_subadditive measure_measure_spmf_conv_measure_pmf measure_pmf.prob_space_axioms pmf.rep_eq prob_space_def sets_measure_pmf singleton_conv)
qed

lemma measure_spmf_eq_measure_pmf_succeeds_and_satisfies :
  \<open>\<P>(x in measure_spmf p. P x) =
    \<P>(x in measure_pmf p. succeeds_and_satisfies P x)\<close>
  by (auto
    intro: arg_cong[where f = \<open>measure_pmf.prob p\<close>]
    split: option.splits
    simp add: space_measure_spmf measure_measure_spmf_conv_measure_pmf)

abbreviation (input) kleisli_compose_left ::
  \<open>('a \<Rightarrow> 'b spmf) \<Rightarrow> ('b \<Rightarrow> 'c spmf) \<Rightarrow> 'a \<Rightarrow> 'c spmf\<close>
  (infixl \<open>>=>\<close> 50) where
  \<open>(f >=> g) \<equiv> \<lambda> x. bind_spmf (f x) g\<close>

abbreviation (input) kleisli_compose_right ::
  \<open>('b \<Rightarrow> 'c spmf) \<Rightarrow> ('a \<Rightarrow> 'b spmf) \<Rightarrow> 'a \<Rightarrow> 'c spmf\<close>
  (infixr \<open><=<\<close> 50) where
  \<open>(f <=< g) \<equiv> g >=> f\<close>

end