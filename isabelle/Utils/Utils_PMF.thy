theory Utils_PMF

imports
  "HOL-Probability.Probability_Mass_Function"

begin

fun foldM_pmf :: "('a \<Rightarrow> 'b \<Rightarrow> 'b pmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b pmf" where
  "foldM_pmf _ [] val = return_pmf val" |
  "foldM_pmf f (x # xs) val = f x val \<bind> foldM_pmf f xs"

definition map_option_pmf :: "
  ('a \<Rightarrow> 'b) \<Rightarrow> 'a option pmf \<Rightarrow> 'b option pmf" where
  [simp] : "map_option_pmf \<equiv> map_pmf \<circ> map_option"

lemma bernoulli_pmf_one [simp] :
  "bernoulli_pmf 1 = return_pmf True"
  by (simp add: bernoulli_pmf.rep_eq pmf_eqI)

lemma binomial_pmf_one [simp] :
  "binomial_pmf n 1 = return_pmf n"
  by (metis set_pmf_binomial_1 set_pmf_subset_singleton subset_iff_psubset_eq) 

lemma map_pmf_times_one [simp] :
  fixes p :: "nat pmf"
  shows "map_pmf ((*) (Suc 0)) p = p"
  by (simp add: pmf.map_ident_strong) 

end