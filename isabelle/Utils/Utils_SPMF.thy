theory Utils_SPMF

imports
  "HOL-Probability.SPMF"
  CVM.Utils_Function

begin

sledgehammer_params [
  (* verbose = true, *)
  minimize = true,
  preplay_timeout = 15,
  timeout = 60,
  max_facts = smart,
  provers = "
    cvc4 z3 verit
    e vampire spass
  "
]

abbreviation fail_spmf :: "'a spmf" where
  "fail_spmf \<equiv> return_pmf None"

definition prob_fail :: "'a spmf \<Rightarrow> real" where
  "prob_fail \<equiv> flip pmf None"

fun
  foldM_spmf :: "
    ('a \<Rightarrow> 'b \<Rightarrow> 'b spmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b spmf" where "
  foldM_spmf _ [] acc = return_spmf acc" | "
  foldM_spmf f (x # xs) acc = f x acc \<bind> foldM_spmf f xs"

end