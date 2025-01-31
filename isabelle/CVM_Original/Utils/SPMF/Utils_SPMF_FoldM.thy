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
  \<open>foldM_spmf (\<lambda> x. spmf_of_pmf <<< f x) xs val = spmf_of_pmf (foldM_pmf f xs val)\<close>
  apply (induction xs)
  by (simp_all add: spmf_of_pmf_bind)

lemma pmf_foldM_spmf_nil :
  \<open>spmf (foldM_spmf f [] acc) acc' = of_bool (acc = acc')\<close>
  by simp

lemma pmf_foldM_spmf_cons :
  \<open>pmf (foldM_spmf f (x # xs) acc) a =
    \<integral> acc'. (
      case acc' of
        None \<Rightarrow> pmf fail_spmf a |
        Some acc' \<Rightarrow> pmf (foldM_spmf f xs acc') a)
      \<partial> f x acc\<close>
  apply (simp add: bind_spmf_def pmf_bind)
  by (metis (mono_tags, lifting) option.case_eq_if)

lemma integrable_prob_fail_foldM_spmf :
  \<open>integrable
    (measure_spmf <| f x acc) <|
    prob_fail <<< foldM_spmf f xs\<close>
  by (auto
    intro: measure_spmf.integrable_const_bound[where B = 1]
    simp add: pmf_le_1)

end