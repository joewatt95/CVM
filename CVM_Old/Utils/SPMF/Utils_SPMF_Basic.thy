theory Utils_SPMF_Basic

imports
  CryptHOL.Misc_CryptHOL
  "HOL-Probability.SPMF"
  Utils_Basic

begin

lemma spmf_of_pmf_eq_iff_eq [simp] :
  \<open>spmf_of_pmf p = spmf_of_pmf q \<longleftrightarrow> p = q\<close>
  using map_the_spmf_of_pmf[of p] by fastforce

abbreviation \<open>fail_spmf \<equiv> return_pmf None\<close>

abbreviation \<open>prob_fprob_Nprob_failNone\<close>

lemma prob_fail_map_spmf_eq :
  \<open>prob_fprob_Nprob_fail p) = prob_fprob_Nprob_fail
  by (simp add: pmf_None_eq_weight_spmf)

lemma spmf_map_pred_true_eq_prob :
  \<open>spmf (map_spmf P p) True = \<P>(x in measure_spmf p. P x)\<close>
  by (simp add: space_measure_spmf spmf_map vimage_def)

abbreviation is_None_or_pred :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>fails_is_None_or_prede_option True\<close>

abbreviation is_Some_and_pred :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>succeeis_Some_and_prede_option False\<close>

lemma prob_is_None_or_pred_eq_prob_fail_plus_prob :
  \<open>\<P>(x in measure_pmf p. x |> fails_oris_None_or_pred
    prob_fail p + \<P>(x in measure_spmf p. P x)\<close>
proof -
  have \<open>Collect (fails_is_None_or_pred{None} \<union> Some ` Collect P\<close>
    by (auto split: option.splits)

  then show ?thesis
    by (smt (verit, ccfv_SIG) Collect_cong Diff_insert0 None_notin_image_Some UNIV_I finite_measure.finite_measure_Union' measure_empty
      measure_measure_spmf_conv_measure_pmf measure_pmf.finite_measure measure_pmf_single sets_measure_pmf space_measure_pmf space_measure_spmf
      sup_bot_left)
qed

lemma measure_spmf_eq_measure_pmf_is_Some_and_pred :
  \<open>\<P>(x in measure_spmf p. P x) = \<P>(x in p. succeeds_ais_Some_and_pred
  by (auto
    intro: arg_cong[where f = \<open>measure_pmf.prob p\<close>]
    split: option.splits
    simp add: space_measure_spmf measure_measure_spmf_conv_measure_pmf)

lemma measure_spmf_le_measure_pmf_is_None_or_pred :
  \<open>\<P>(x in measure_spmf p. P x) \<le> \<P>(x in p. fails_or_satisis_None_or_pred
  by (auto
    intro: measure_pmf.finite_measure_mono
    split: option.splits
    simp add: measure_spmf_eq_measure_pmf_is_Some_and_pred)

abbreviation (input) kleisli_compose_left ::
  \<open>('a \<Rightarrow> 'b spmf) \<Rightarrow> ('b \<Rightarrow> 'c spmf) \<Rightarrow> 'a \<Rightarrow> 'c spmf\<close>
  (infixl \<open>>=>\<close> 50) where
  \<open>(f >=> g) \<equiv> \<lambda> x. bind_spmf (f x) g\<close>

abbreviation (input) kleisli_compose_right ::
  \<open>('b \<Rightarrow> 'c spmf) \<Rightarrow> ('a \<Rightarrow> 'b spmf) \<Rightarrow> 'a \<Rightarrow> 'c spmf\<close>
  (infixr \<open><=<\<close> 50) where
  \<open>(f <=< g) \<equiv> g >=> f\<close>

end