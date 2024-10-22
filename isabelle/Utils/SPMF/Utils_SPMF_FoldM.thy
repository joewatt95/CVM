theory Utils_SPMF_FoldM

imports
  CVM.Utils_PMF_Common
  CVM.Utils_SPMF_Common

begin

abbreviation foldM_spmf
  :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b spmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close> where
  \<open>foldM_spmf \<equiv> foldM bind_spmf return_spmf\<close>

abbreviation foldM_spmf_enumerate where
  \<open>foldM_spmf_enumerate \<equiv> foldM_enumerate bind_spmf return_spmf\<close>

lemma foldM_spmf_eq_foldM_pmf_case :
  \<open>foldM_spmf f xs =
    foldM_pmf
      (\<lambda> x. case_option fail_spmf (f x))
      xs <<< Some\<close>
  (is \<open>_ = Some >>> ?foldM_pmf\<close>)
proof -
  have
    \<open>?foldM_pmf = case_option fail_spmf (foldM_spmf f xs)\<close>
    apply (induction xs)
    apply (metis fail_spmf_def foldM.simps(1) not_None_eq option.simps(4) option.simps(5)) 
    by (metis (mono_tags, lifting) bind_return_pmf bind_spmf_def fail_spmf_def foldM.simps(2) not_None_eq option.simps(4) return_bind_spmf)

  then show ?thesis by (metis option.simps(5))
qed

lemma spmf_of_pmf_foldM_pmf_eq_foldM_spmf :
  \<open>spmf_of_pmf <<< foldM_pmf f xs = foldM_spmf (\<lambda> x. spmf_of_pmf <<< f x) xs\<close>
  apply (induction xs) by (simp_all add: spmf_of_pmf_bind)

lemma pmf_foldM_spmf_nil :
  shows
    \<open>spmf (foldM_spmf f [] acc) acc = 1\<close>
    \<open>acc \<noteq> acc' \<Longrightarrow> spmf (foldM_spmf f [] acc) acc' = 0\<close>
  by simp_all

lemma pmf_foldM_spmf_cons :
  \<open>pmf (foldM_spmf f (x # xs) acc) a
  = \<integral> acc'. (
      case acc' of
        None \<Rightarrow> pmf fail_spmf a |
        Some acc' \<Rightarrow> pmf (foldM_spmf f xs acc') a)
      \<partial> f x acc\<close>
  apply (simp add: bind_spmf_def pmf_bind)
  by (metis fail_spmf_def option.case_eq_if)

lemma integrable_prob_fail_foldM_spmf :
  \<open>integrable
    (measure_spmf <| f x acc) <|
    prob_fail <<< foldM_spmf f xs\<close>
  by (auto
      intro: measure_spmf.integrable_const_bound[where ?B = 1]
      simp add: prob_fail_def pmf_le_1)

lemma foldM_spmf_lossless_of_always_lossless :
  assumes \<open>\<And> x acc. lossless_spmf <| f x acc\<close>
  shows \<open>lossless_spmf <| foldM_spmf f xs acc\<close>
  apply (induction xs arbitrary: acc)
  using assms by auto

end