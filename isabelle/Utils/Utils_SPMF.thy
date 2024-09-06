theory Utils_SPMF

imports
  "HOL-Probability.SPMF"

begin

abbreviation fail_spmf :: "'a spmf" where
  "fail_spmf \<equiv> return_pmf None"

end