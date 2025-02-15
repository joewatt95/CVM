theory Utils_SPMF_Basic

imports
  "HOL-Probability.SPMF"
  Utils_Basic

begin

lemma integrable_measure_spmf_pmf [simp] :
  \<open>integrable (measure_spmf p) <| \<lambda> x. pmf (f x) y\<close>
  apply (intro measure_spmf.integrable_const_bound[where B = 1])
  by (simp_all add: pmf_le_1)

lemma spmf_of_pmf_eq_iff_eq [simp] :
  \<open>spmf_of_pmf p = spmf_of_pmf q \<longleftrightarrow> p = q\<close>
  by (metis measure_pmf_inject measure_spmf_spmf_of_pmf)

abbreviation \<open>fail_spmf \<equiv> return_pmf None\<close>

abbreviation \<open>prob_fail \<equiv> flip pmf None\<close>

lemma prob_fail_map_spmf_eq [simp] :
  \<open>prob_fail (map_spmf f p) = prob_fail p\<close>
  by (simp add: pmf_None_eq_weight_spmf)

lemma spmf_map_pred_true_eq_prob :
  \<open>spmf (map_spmf P p) True = \<P>(x in measure_spmf p. P x)\<close>
  by (simp add: space_measure_spmf spmf_map vimage_def)

abbreviation is_None_or_pred :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>is_None_or_pred \<equiv> case_option True\<close>

abbreviation is_Some_and_pred :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>is_Some_and_pred \<equiv> case_option False\<close>

lemma prob_is_None_or_pred_eq_prob_fail_plus_prob :
  \<open>\<P>(x in measure_pmf p. x |> is_None_or_pred P) =
    prob_fail p + \<P>(x in measure_spmf p. P x)\<close>
proof -
  have \<open>Collect (is_None_or_pred P) = {None} \<union> Some ` Collect P\<close>
    by (auto split: option.splits)

  then show ?thesis
    by (smt (verit, ccfv_SIG) Collect_cong Diff_insert0 None_notin_image_Some UNIV_I finite_measure.finite_measure_Union' measure_empty
      measure_measure_spmf_conv_measure_pmf measure_pmf.finite_measure measure_pmf_single sets_measure_pmf space_measure_pmf space_measure_spmf
      sup_bot_left)
qed

lemma AE_measure_spmf_iff_AE_measure_pmf :
  \<open>(AE x in measure_spmf p. P x) \<longleftrightarrow>
    (AE x in measure_pmf p. is_None_or_pred P x)\<close>
  by (auto
    simp add: AE_measure_pmf_iff in_set_spmf
    split: option.splits)

lemma measure_spmf_eq_measure_pmf_is_Some_and_pred :
  \<open>\<P>(x in measure_spmf p. P x) = \<P>(x in p. is_Some_and_pred P x)\<close>
  by (auto
    intro: arg_cong[where f = \<open>measure_pmf.prob p\<close>]
    split: option.splits
    simp add: space_measure_spmf measure_measure_spmf_conv_measure_pmf)

lemma measure_spmf_le_measure_pmf_is_None_or_pred :
  \<open>\<P>(x in measure_spmf p. P x) \<le> \<P>(x in p. is_None_or_pred P x)\<close>
  by (auto
    intro: measure_pmf.finite_measure_mono
    split: option.splits
    simp add: measure_spmf_eq_measure_pmf_is_Some_and_pred)

end