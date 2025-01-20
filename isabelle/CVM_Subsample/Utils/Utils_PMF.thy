theory Utils_PMF

imports
  "HOL-Probability.Probability_Mass_Function"
  CVM_Subsample.Utils_Basic

begin

abbreviation foldM_pmf ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b pmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b pmf\<close> where
  \<open>foldM_pmf \<equiv> foldM bind_pmf return_pmf\<close>

lemma foldM_pmf_snoc: "foldM_pmf f (xs@[y]) val = bind_pmf (foldM_pmf f xs val) (f y)"
  by (induction xs arbitrary:val)
    (simp_all add: bind_return_pmf bind_return_pmf' bind_assoc_pmf cong:bind_pmf_cong)

end