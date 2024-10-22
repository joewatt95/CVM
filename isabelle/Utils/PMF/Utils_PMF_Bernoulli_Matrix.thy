theory Utils_PMF_Bernoulli_Matrix

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Finite_Fields.Finite_Fields_More_PMF
  CVM.Utils_PMF_Common

begin

definition bernoulli_matrix ::
  \<open>nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (nat \<times> nat \<Rightarrow> bool) pmf\<close> where
  \<open>bernoulli_matrix m n p \<equiv>
    prod_pmf ({..< m} \<times> {..< n}) \<lblot>bernoulli_pmf p\<rblot>\<close>

abbreviation
  \<open>fair_bernoulli_matrix m n \<equiv> bernoulli_matrix m n (1 / 2)\<close>

lemma bernoulli_matrix_eq_uncurry_prod :
  fixes m n :: nat
  defines
    [simp] : \<open>m' \<equiv> {..< m}\<close> and 
    [simp] : \<open>n' \<equiv> {..< n}\<close>
  shows
    \<open>bernoulli_matrix m n p = (
      prod_pmf n' \<lblot>prod_pmf m' \<lblot>bernoulli_pmf p\<rblot>\<rblot>
        |> map_pmf (\<lambda> \<omega>. \<lambda> (x, y) \<in> m' \<times> n'. \<omega> y x))\<close>
  by (auto
    intro!: map_pmf_cong
    simp add:
      bernoulli_matrix_def
      prod_pmf_swap[of m' n', simplified]
      prod_pmf_uncurry[of n' m', simplified]
      map_pmf_comp fun_eq_iff)

end