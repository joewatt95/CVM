theory Distinct_Elems_Error_Bounds_Common

imports
  CVM.Distinct_Elems_Algo
  CVM.Utils_PMF_Bernoulli_Binomial

begin

locale with_threshold_r_l_\<epsilon>_xs = with_threshold +
  fixes
    r l :: nat and
    \<epsilon> :: real and
    xs :: \<open>'a list\<close>
begin

abbreviation
  \<open>run_with_bernoulli_matrix f \<equiv>
    map_pmf (f xs) (fair_bernoulli_matrix (length xs) (length xs))\<close>

end

locale with_threshold_pos_r_l_\<epsilon>_xs =
  with_threshold_r_l_\<epsilon>_xs +
  with_threshold_pos

end