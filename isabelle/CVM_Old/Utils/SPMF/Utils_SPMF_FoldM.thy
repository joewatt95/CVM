theory Utils_SPMF_FoldM

imports
  Constructive_Cryptography_CM.Fold_Spmf
  Utils_PMF_Basic
  Utils_SPMF_Basic

begin

abbreviation foldM_spmf ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b spmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close> where
  \<open>foldM_spmf \<equiv> foldM bind_spmf return_spmf\<close>

abbreviation
  \<open>foldM_spmf_enumerate \<equiv> foldM_enumerate bind_spmf return_spmf\<close>

lemma foldM_spmf_eq_foldl_spmf :
  \<open>foldM_spmf f xs val = foldl_spmf (flip f) (return_spmf val) xs\<close>
  apply (induction xs arbitrary: val)
  by (simp_all add: bind_foldl_spmf_return bind_spmf_cong)

lemma foldM_spmf_eq_foldM_pmf_case :
  \<open>foldM_spmf f xs =
    foldM_pmf
      (\<lambda> x. case_option fail_spmf (f x))
      xs <<< Some\<close>
  (is \<open>_ = Some >>> ?foldM_pmf\<close>)
proof -
  have \<open>?foldM_pmf = case_option fail_spmf (foldM_spmf f xs)\<close>
  proof (induction xs)
    case Nil
    then show ?case
      by (metis bind_return_pmf bind_return_spmf bind_spmf_def foldM_empty)
  next
    case (Cons _ _)
    then show ?case
      by (metis (mono_tags, lifting) bind_spmf_def foldM.simps(2) not_None_eq option.case(1,2) return_None_bind_spmf)
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