theory Props_Basic

imports
  "HOL-Probability.Product_PMF"
  CVM.Utils_Function
  CVM.Utils_PMF
  CVM.Utils_Real

begin

abbreviation eps_del_approxs ("_ \<approx> \<langle> _ , _ \<rangle> _") where "
  (f \<approx>\<langle>\<epsilon>, \<delta>\<rangle> x) \<equiv>
    \<P>(\<omega> in measure_pmf f. \<omega> / x \<in> {1 - \<epsilon> .. 1 + \<epsilon>})
    \<ge> 1 - \<delta>"

definition estimate_size :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> real pmf" where
  [simp] : "
  estimate_size universe chi k \<equiv> (
    let
      estimate_size_with :: ('a \<Rightarrow> bool) \<Rightarrow> nat = \<lambda> keep_in_chi.
        let chi = Set.filter keep_in_chi chi
        in card chi * 2 ^ k;

      keep_in_chi :: ('a \<Rightarrow> bool) pmf =
        Pi_pmf universe undefined <| \<lambda> _. bernoulli_pmf (1 / 2 ^ k)

    in map_pmf estimate_size_with keep_in_chi)"

lemma estimate_size_approx_correct :
  fixes
    \<epsilon> \<delta> threshold :: real and
    k :: nat and
    universe chi :: "'a set"
  defines "chi_size :: real \<equiv> card chi"
  assumes "
    finite universe" and "
    chi \<subseteq> universe" and "
    k \<in> {log2 (chi_size / threshold) .. log2 chi_size}"
  shows "
    (estimate_size universe chi k) \<approx>\<langle>\<epsilon>, \<delta>\<rangle> chi_size"
  sorry

end