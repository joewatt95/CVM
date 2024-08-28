theory Props_Basic

imports
  "HOL-Probability.Product_PMF"
  CVM.Utils_Function
  CVM.Utils_PMF
  CVM.Utils_Real

begin

abbreviation eps_del_approxs ("_ \<approx> \<langle> _ , _ \<rangle> _") where "
  (f \<approx>\<langle>\<epsilon>, \<delta>\<rangle> x) \<equiv>
    \<P>(\<omega> in measure_pmf f. \<bar>\<omega> - x\<bar> \<le> \<delta> * x)
    \<ge> 1 - \<epsilon>"

definition estimate_size :: "nat \<Rightarrow> 'a set \<Rightarrow> real pmf" where "
  estimate_size k chi \<equiv> (
    let
      estimate_size_with :: ('a \<Rightarrow> bool) \<Rightarrow> nat = \<lambda> pred.
        let chi = Set.filter pred chi
        in card chi * 2 ^ k;

      keep_in_chi :: ('a \<Rightarrow> bool) pmf =
        Pi_pmf UNIV undefined <| \<lambda> _. bernoulli_pmf (1 / 2 ^ k)

    in map_pmf estimate_size_with keep_in_chi)"

lemma estimate_size_approx_correct :
  fixes
    \<epsilon> \<delta> threshold :: real and
    k :: nat and
    chi :: "'a set"
  defines "chi_size :: real \<equiv> card chi"
  assumes "
    k \<in> {log2 (chi_size / threshold) .. log2 chi_size}"
  shows "
    (estimate_size k chi) \<approx>\<langle>\<epsilon>, \<delta>\<rangle> chi_size"
  sorry

end