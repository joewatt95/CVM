theory Final_Algo

imports
  "HOL-Probability.Product_PMF"
  CVM.Utils_Function

begin

definition estimate_distinct :: \<open>nat \<Rightarrow> 'a set \<Rightarrow> real pmf\<close> where
  \<open>estimate_distinct k chi \<equiv> (
    let
      estimate_distinct_with :: ('a \<Rightarrow> bool) \<Rightarrow> nat = \<lambda> keep_in_chi.
        let chi = Set.filter keep_in_chi chi
        in card chi * 2 ^ k;

      keep_in_chi :: ('a \<Rightarrow> bool) pmf =
        Pi_pmf chi undefined <| \<lambda> _. bernoulli_pmf (1 / 2 ^ k)

    in map_pmf estimate_distinct_with keep_in_chi)\<close>

end