theory Utils_SPMF_FoldM

imports
  "CVM.Utils_SPMF_Common"

begin

fun
  foldM_spmf :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b spmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close> where
  \<open>foldM_spmf _ [] acc = return_spmf acc\<close> |
  \<open>foldM_spmf f (x # xs) acc = f x acc \<bind> foldM_spmf f xs\<close>

locale spmf_foldM =
  fixes
    f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close> and
    x :: 'a and
    xs :: \<open>'a list\<close> and
    acc :: 'b
begin

lemma pmf_foldM_spmf_nil :
  shows
    \<open>spmf (foldM_spmf f [] acc) acc = 1\<close> and
    \<open>acc \<noteq> acc' \<Longrightarrow> spmf (foldM_spmf f [] acc) acc' = 0\<close>
  by auto

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
    prob_fail <<< (foldM_spmf f xs)\<close>

  by (auto
      intro!: measure_spmf.integrable_const_bound[where ?B = 1]
      simp add: prob_fail_def pmf_le_1)

lemma foldM_spmf_lossless_of_always_lossless :
  assumes \<open>\<And> x acc. lossless_spmf <| f x acc\<close>
  shows \<open>lossless_spmf <| foldM_spmf f xs acc\<close>

  apply (induction xs arbitrary: acc)
  using assms by auto

end

end