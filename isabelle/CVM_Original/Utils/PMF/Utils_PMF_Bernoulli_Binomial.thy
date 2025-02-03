theory Utils_PMF_Bernoulli_Binomial

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Finite_Fields.Finite_Fields_More_PMF
  Utils_PMF_Basic

begin

lemma bernoulli_pmf_0_1 [simp] :
  \<open>bernoulli_pmf 0 = return_pmf False\<close>
  \<open>bernoulli_pmf 1 = return_pmf True\<close>
  by (simp_all add: bernoulli_pmf.rep_eq pmf_eqI)

lemma
  binomial_pmf_p_0 [simp] : \<open>binomial_pmf n 0 = return_pmf 0\<close> and
  binomial_pmf_p_1 [simp] : \<open>binomial_pmf n 1 = return_pmf n\<close>
  using set_pmf_subset_singleton by fastforce+

context
  fixes p :: real
  assumes \<open>0 \<le> p\<close> \<open>p \<le> 1\<close>
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

  with assms \<open>0 \<le> p\<close> \<open>p \<le> 1\<close> show ?thesis
    by (auto
      intro: pmf_eqI
      simp add: mult_le_one bernoulli_pmf.rep_eq pmf_bind)
qed

lemma bernoulli_eq_map_Pi_pmf_aux : 
  assumes \<open>card I = Suc k\<close>
  shows
    \<open>bernoulli_pmf (p ^ Suc k) = (
      \<lblot>bernoulli_pmf p\<rblot>
        |> Pi_pmf I dflt
        |> map_pmf (Ball I))\<close>
using assms proof (induction k arbitrary: I)
  case 0
  then show ?case
    by (auto simp add:
      \<open>0 \<le> p\<close> \<open>p \<le> 1\<close> Pi_pmf_singleton card_1_singleton_iff map_pmf_comp)
next
  case (Suc k)

  then obtain x J where
    \<open>finite J\<close> \<open>card J = Suc k\<close> \<open>I = insert x J\<close> \<open>x \<notin> J\<close>
    by (metis card_Suc_eq_finite)

  with
    Suc.IH[of J] \<open>0 \<le> p\<close> \<open>p \<le> 1\<close> power_le_one[of p]
    bernoulli_pmf_eq_bernoulli_pmfs[of \<open>p ^ Suc k\<close>]
  show ?case
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
    assms \<open>0 \<le> p\<close> \<open>p \<le> 1\<close>
    bernoulli_eq_map_Pi_pmf_aux[of I \<open>card I - 1\<close> dflt]
    Pi_pmf_subset[of J I dflt \<open>\<lblot>bernoulli_pmf p\<rblot>\<close>]
  by (fastforce simp add: map_pmf_comp)

end

abbreviation bernoulli_nat_pmf :: \<open>real \<Rightarrow> nat pmf\<close> where
 \<open>bernoulli_nat_pmf \<equiv> bernoulli_pmf >>> map_pmf of_bool\<close>

context binomial_distribution
begin

abbreviation Pi_bernoulli_nat_pmf :: \<open>(nat \<Rightarrow> nat) pmf\<close> where
  \<open>Pi_bernoulli_nat_pmf \<equiv> Pi_pmf {..< n} 0 \<lblot>bernoulli_nat_pmf p\<rblot>\<close>

lemma binomial_pmf_eq_map_sum_of_bernoullis :
  \<open>binomial_pmf n p = (
    Pi_bernoulli_nat_pmf
      |> map_pmf (\<lambda> P. \<Sum> m < n. P m))\<close>
  using p
  by (simp add:
    map_pmf_comp Collect_conj_eq lessThan_def
    binomial_pmf_altdef'[where A = \<open>{..< n}\<close> and dflt = undefined]
    Pi_pmf_map'[where dflt' = undefined])

lemma expectation_binomial_pmf :
  \<open>measure_pmf.expectation (binomial_pmf n p) id = n * p\<close>
  using p
  by (simp add:
    binomial_pmf_eq_map_sum_of_bernoullis
    expectation_sum_Pi_pmf integrable_measure_pmf_finite)

end

definition bernoulli_matrix ::
  \<open>nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (nat \<times> nat \<Rightarrow> bool) pmf\<close> where
  \<open>bernoulli_matrix m n p \<equiv>
    prod_pmf ({..< m} \<times> {..< n}) \<lblot>bernoulli_pmf p\<rblot>\<close>

abbreviation
  \<open>fair_bernoulli_matrix m n \<equiv> bernoulli_matrix m n (1 / 2)\<close>

lemma
  fixes m n
  defines \<open>m' \<equiv> {..< m}\<close> and \<open>n' \<equiv> {..< n}\<close>
  shows
    bernoulli_matrix_eq_uncurry_prod :
      \<open>bernoulli_matrix m n p = (
        prod_pmf m' \<lblot>prod_pmf n' \<lblot>bernoulli_pmf p\<rblot>\<rblot>
          |> map_pmf (\<lambda> \<omega>. \<lambda> (x, y) \<in> m' \<times> n'. \<omega> x y))\<close> (is ?thesis_0) and

    bernoulli_matrix_eq_uncurry_prod' :
      \<open>bernoulli_matrix m n p = (
        prod_pmf n' \<lblot>prod_pmf m' \<lblot>bernoulli_pmf p\<rblot>\<rblot>
          |> map_pmf (\<lambda> \<omega>. \<lambda> (x, y) \<in> m' \<times> n'. \<omega> y x))\<close> (is ?thesis_1)
proof -
  show ?thesis_0
    unfolding bernoulli_matrix_def m'_def n'_def
    by (auto simp add: prod_pmf_uncurry)

  thm prod_pmf_uncurry prod_pmf_swap

  then show ?thesis_1
    unfolding m'_def n'_def
    thm trans[OF prod_pmf_uncurry[symmetric] prod_pmf_swap]
    apply (simp add: trans[OF prod_pmf_uncurry[symmetric] prod_pmf_swap])
    sorry
qed

end