theory Utils_SPMF_FoldM

imports
  Utils_PMF_Basic
  Utils_SPMF_Basic

begin

abbreviation foldM_spmf ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b spmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close> where
  \<open>foldM_spmf \<equiv> foldM bind_spmf return_spmf\<close>

abbreviation
  \<open>foldM_spmf_enumerate \<equiv> foldM_enumerate bind_spmf return_spmf\<close>

lemma foldM_spmf_eq_foldM_pmf_case :
  \<open>foldM_spmf f xs = foldM_pmf (case_option fail_spmf <<< f) xs <<< Some\<close>
  (is \<open>_ = Some >>> ?foldM_pmf\<close>)
proof -
  have \<open>?foldM_pmf = case_option fail_spmf (foldM_spmf f xs)\<close>
  proof (induction xs)
    case Nil
    then show ?case
      by (metis bind_return_pmf foldM.simps(1) try_spmf_def try_spmf_return_pmf_None2)
  next
    case (Cons _ _)
    then show ?case
      apply (intro ext)
      apply (simp split: option.splits)
      by (simp add: bind_return_pmf bind_spmf_def)
  qed

  then show ?thesis by simp 
qed

lemma foldM_spmf_of_pmf_eq :
  \<open>foldM_spmf (\<lambda> x. spmf_of_pmf <<< f x) xs = spmf_of_pmf <<< foldM_pmf f xs\<close>
  (is ?thesis_0)
  \<open>foldM_spmf (\<lambda> x. spmf_of_pmf <<< f x) xs val = spmf_of_pmf (foldM_pmf f xs val)\<close>
  (is ?thesis_1)
proof -
  show ?thesis_0
    apply (induction xs)
    by (simp_all add: spmf_of_pmf_bind)

  then show ?thesis_1 by simp
qed

lemma pmf_foldM_spmf_nil :
  \<open>pmf (foldM_spmf f [] val) val' = of_bool (Some val = val')\<close>
  by simp

lemma pmf_foldM_spmf_cons :
  \<open>pmf (foldM_spmf f (x # xs) val) y =
    measure_pmf.expectation (f x val) (
      \<lambda> val'. case val' of
        None \<Rightarrow> of_bool (y = None) |
        Some val' \<Rightarrow> pmf (foldM_spmf f xs val') y)\<close>
  unfolding foldM.simps bind_spmf_def pmf_bind
  apply (intro integral_cong_AE)
  by (auto simp add: AE_measure_pmf_iff split: option.splits)

end