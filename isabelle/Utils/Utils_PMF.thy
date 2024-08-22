theory Utils_PMF

imports
  Main
  "HOL-Probability.Probability_Mass_Function"

begin

primrec foldM_pmf :: "('a \<Rightarrow> 'b \<Rightarrow> 'b pmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b pmf" where
  "foldM_pmf _ [] val = return_pmf val" |
  "foldM_pmf f (x # xs) val = f x val \<bind> foldM_pmf f xs"

end