theory Utils_PMF_Bernoulli_Binomial

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Finite_Fields.Finite_Fields_More_PMF
  CVM.Utils_PMF_Common

begin

declare [[coercion \<open>of_bool :: bool \<Rightarrow> nat\<close>]]

lemma bernoulli_pmf_of_bool [simp] :
  \<open>bernoulli_pmf b = return_pmf b\<close>
  by (simp add: bernoulli_pmf.rep_eq pmf_eqI)

lemma binomial_pmf_one [simp] :
  \<open>binomial_pmf n 1 = return_pmf n\<close>
  by (metis set_pmf_binomial_1 set_pmf_subset_singleton subset_iff_psubset_eq)

context
  fixes p :: real
  assumes p_betw_0_1 : \<open>0 \<le> p\<close> \<open>p \<le> 1\<close>
begin

lemma bernoulli_pmf_eq_bernoulli_pmfs :
  assumes \<open>0 \<le> p'\<close> \<open>p' \<le> 1\<close>
  shows
    \<open>bernoulli_pmf (p * p') = do {
      b \<leftarrow> bernoulli_pmf p;
      b' \<leftarrow> bernoulli_pmf p';
      return_pmf <| b \<and> b' }\<close>
proof -
  have \<open>- (p * p') = (1 - p') * p - p\<close> by argo

  then show ?thesis
    using assms p_betw_0_1
    by (auto
      intro: pmf_eqI
      simp add: mult_le_one bernoulli_pmf.rep_eq pmf_bind)
qed

lemma bernoulli_eq_map_Pi_pmf_aux : 
  \<open>card I = Suc k \<Longrightarrow>
  bernoulli_pmf (p ^ Suc k) = (
    \<lblot>bernoulli_pmf p\<rblot>
      |> Pi_pmf I dflt
      |> map_pmf (Ball I))\<close>
proof (induction k arbitrary: I)
  case 0
  then show ?case
    by (auto simp add:
      p_betw_0_1 Pi_pmf_singleton card_1_singleton_iff map_pmf_comp)
next
  case (Suc k)

  then obtain x J where
    \<open>finite J\<close> \<open>card J = Suc k\<close> \<open>I = insert x J\<close> \<open>x \<notin> J\<close>
    by (metis card_Suc_eq_finite)

  moreover note
    Suc.IH[of J] p_betw_0_1 power_le_one[of p]
    bernoulli_pmf_eq_bernoulli_pmfs[of \<open>p ^ Suc k\<close>]

  ultimately show ?case
    by (fastforce
      intro: bind_pmf_cong
      simp add: Pi_pmf_insert' map_bind_pmf bind_map_pmf)
qed

text
  \<open>This says that to simulate a coin flip with the probability of getting H as
  p ^ k, we can flip \<ge> k coins with probability p of getting H, and check if
  any k of them are H. 

  More precisely, a bernoulli RV with probability p ^ k (k > 0) is equivalent
  to doing the following:
  1. We fix a (finite) family of indices J, and a subset I \<subseteq> J of cardinality k.
  2. We construct a family of IID bernoulli RVs of probability p,
     indexed by J, and sample from it.
  3. Viewing the outcome as a characteristic function of J, we check if the
     subset it defines contains I, outputting \<top> iff that is the case.\<close>
lemma bernoulli_eq_map_Pi_pmf :
  assumes
    \<open>card I > 0\<close> \<open>I \<subseteq> J\<close> \<open>finite J\<close>
  shows
    \<open>bernoulli_pmf (p ^ card I) = (
      \<lblot>bernoulli_pmf p\<rblot>
        |> Pi_pmf J dflt
        |> map_pmf (Ball I))\<close>
  using
    assms p_betw_0_1
    bernoulli_eq_map_Pi_pmf_aux[of I \<open>card I - 1\<close> dflt]
    Pi_pmf_subset[of J I dflt \<open>\<lblot>bernoulli_pmf p\<rblot>\<close>]
  by (fastforce simp add: map_pmf_comp)

abbreviation \<open>coerced_bernoulli_pmf \<equiv> bernoulli_pmf >>> map_pmf of_bool\<close>

lemma binomial_pmf_eq_map_sum_of_bernoullis :
  \<open>binomial_pmf n p = (
    \<lblot>coerced_bernoulli_pmf p\<rblot>
      |> prod_pmf {..< n}
      |> map_pmf (\<lambda> P. \<Sum> m < n. P m))\<close>
  by (simp add:
    p_betw_0_1 map_pmf_comp Collect_conj_eq lessThan_def
    binomial_pmf_altdef'[where A = \<open>{..< n}\<close>, where dflt = undefined]
    Pi_pmf_map'[where d' = undefined])

lemma expectation_binomial_pmf:
  \<open>measure_pmf.expectation (binomial_pmf n p) id = n * p\<close>
  by (simp add:
    p_betw_0_1 binomial_pmf_eq_map_sum_of_bernoullis 
    expectation_sum_Pi_pmf integrable_measure_pmf_finite)

end

definition bernoulli_matrix ::
  \<open>nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (nat \<times> nat \<Rightarrow> bool) pmf\<close> where
  \<open>bernoulli_matrix m n p \<equiv>
    prod_pmf ({..< m} \<times> {..< n}) \<lblot>bernoulli_pmf p\<rblot>\<close>

abbreviation
  \<open>fair_bernoulli_matrix m n \<equiv> bernoulli_matrix m n (1 / 2)\<close>

lemma bernoulli_matrix_eq_uncurry_prod :
  fixes m n
  defines
    [simp] : \<open>m' \<equiv> {..< m}\<close> and 
    [simp] : \<open>n' \<equiv> {..< n}\<close>
  shows
    \<open>bernoulli_matrix m n p = (
      prod_pmf n' \<lblot>prod_pmf m' \<lblot>bernoulli_pmf p\<rblot>\<rblot>
        |> map_pmf (\<lambda> \<omega>. \<lambda> (x, y) \<in> m' \<times> n'. \<omega> y x))\<close>
  by (auto
    intro: map_pmf_cong
    simp add:
      bernoulli_matrix_def map_pmf_comp fun_eq_iff
      prod_pmf_swap[of m' n', simplified]
      prod_pmf_uncurry[of n' m', simplified])

end