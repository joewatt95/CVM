theory Utils_SPMF

imports
  "HOL-Probability.SPMF"
  CVM.Utils_Function

begin

abbreviation fail_spmf :: \<open>'a spmf\<close> where
  \<open>fail_spmf \<equiv> return_pmf None\<close>

definition prob_fail :: \<open>'a spmf \<Rightarrow> real\<close> where
  \<open>prob_fail \<equiv> flip pmf None\<close>

fun
  foldM_spmf :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b spmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close> where
  \<open>foldM_spmf _ [] acc = return_spmf acc\<close> |
  \<open>foldM_spmf f (x # xs) acc = f x acc \<bind> foldM_spmf f xs\<close>

thm measure_spmf.integrable_const_bound

lemma integrable_prob_fail_foldM_spmf :
  fixes
    f :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close> and
    x :: 'a and
    xs :: \<open>'a list\<close> and
    acc :: 'b
  shows
    \<open>integrable
      (measure_spmf <| f x acc) <|
      prob_fail <<< (foldM_spmf f xs)\<close>

  by (auto
      intro!: measure_spmf.integrable_const_bound[where ?B = 1]
      simp add: prob_fail_def pmf_le_1)

end