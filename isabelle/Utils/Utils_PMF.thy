theory Utils_PMF

imports
  "HOL-Probability.Probability_Mass_Function"

begin

primrec foldM_pmf :: "('a \<Rightarrow> 'b \<Rightarrow> 'b pmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b pmf" where
  "foldM_pmf _ [] val = return_pmf val" |
  "foldM_pmf f (x # xs) val = f x val \<bind> foldM_pmf f xs"

(*\<bind> 
    bind_pmf (f x val) (foldM_option_pmf f xs)
*)

fun
  foldM_option_pmf :: "
    ('a \<Rightarrow> 'b \<Rightarrow> 'b option pmf) \<Rightarrow>
    'a list \<Rightarrow> 'b option \<Rightarrow> 'b option pmf" where

  "foldM_option_pmf f (x # xs) (Some val) = f x val \<bind> foldM_option_pmf f xs" |
  "foldM_option_pmf _ _ val = return_pmf val"

end