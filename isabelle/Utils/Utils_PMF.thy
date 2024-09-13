theory Utils_PMF

imports
  "HOL-Probability.Probability_Mass_Function"
  CVM.Utils_Function

begin

fun foldM_pmf :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b pmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b pmf\<close> where
  \<open>foldM_pmf _ [] val = return_pmf val\<close> |
  \<open>foldM_pmf f (x # xs) val = f x val \<bind> foldM_pmf f xs\<close>

lemma bernoulli_pmf_one [simp] :
  \<open>bernoulli_pmf 1 = return_pmf True\<close>

  by (simp add: bernoulli_pmf.rep_eq pmf_eqI)

lemma binomial_pmf_one [simp] :
  \<open>binomial_pmf n 1 = return_pmf n\<close>

  by (metis set_pmf_binomial_1 set_pmf_subset_singleton subset_iff_psubset_eq) 

lemma map_pmf_times_one [simp] :
  fixes p :: \<open>nat pmf\<close>
  shows \<open>map_pmf ((*) <| Suc 0) p = p\<close>

  by (simp add: pmf.map_ident_strong) 

end