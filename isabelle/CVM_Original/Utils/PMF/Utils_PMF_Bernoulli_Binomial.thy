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
  assumes p [simp] : \<open>0 \<le> p\<close> \<open>p \<le> 1\<close>
begin

lemma bernoulli_pmf_eq_bernoulli_pmfs :
  assumes \<open>0 \<le> p'\<close> \<open>p' \<le> 1\<close>
  shows
    \<open>bernoulli_pmf (p * p') = do {
      b \<leftarrow> bernoulli_pmf p;
      b' \<leftarrow> bernoulli_pmf p';
      return_pmf <| b \<and> b' }\<close>
  using assms p
  apply (intro pmf_eqI)
  by (simp add: mult_le_one bernoulli_pmf.rep_eq pmf_bind algebra_simps)

lemmas bernoulli_pmf_eq_bernoulli_pmfs' = bernoulli_pmf_eq_bernoulli_pmfs[
  simplified map_pmf_def[symmetric]]

private lemma bernoulli_eq_map_Pi_pmf_aux : 
  assumes \<open>card I = Suc k\<close>
  shows
    \<open>bernoulli_pmf (p ^ Suc k) = (
      \<lblot>bernoulli_pmf p\<rblot>
        |> Pi_pmf I dflt
        |> map_pmf (Ball I))\<close>
    (is \<open>?L k = ?R I\<close>)
using assms proof (induction k arbitrary: I)
  case 0
  then show ?case
    by (auto simp add: Pi_pmf_singleton card_1_singleton_iff map_pmf_comp)
next
  case (Suc k)
  moreover from calculation obtain x J where
    \<open>finite J\<close> \<open>card J = Suc k\<close> \<open>I = insert x J\<close> \<open>x \<notin> J\<close>
    by (metis card_Suc_eq_finite)

  moreover from calculation have
    \<open>?L (Suc k)  = do {
      b \<leftarrow> bernoulli_pmf p;
      b' \<leftarrow> ?R J;
      return_pmf <| b \<and> b' }\<close>
    by (simp add: bernoulli_pmf_eq_bernoulli_pmfs mult_le_one power_le_one_iff)

  moreover from calculation
  have \<open>\<dots> = ?R (insert x J)\<close>
    apply (subst Pi_pmf_insert')
    by (auto
      intro: bind_pmf_cong map_pmf_cong
      simp flip: map_pmf_def
      simp add: map_pmf_comp map_bind_pmf)

  ultimately show ?case by simp
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
  assumes \<open>finite J\<close> \<open>card I > 0\<close> \<open>I \<subseteq> J\<close>
  shows
    \<open>bernoulli_pmf (p ^ card I) = (
      \<lblot>bernoulli_pmf p\<rblot>
        |> Pi_pmf J dflt
        |> map_pmf (Ball I))\<close>
  using
    assms p 
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
  (is \<open>?L = ?R\<close>)
proof -
  from p have \<open>?L = (
    prod_pmf {..< n} \<lblot>bernoulli_pmf p\<rblot>
      |> map_pmf (\<lambda> P. card {m. m < n \<and> P m}))\<close>
    apply (subst binomial_pmf_altdef'[where A = \<open>{..< n}\<close> and dflt = undefined])
    by simp_all

  also have \<open>\<dots> = ?R\<close>
    unfolding Pi_pmf_map'[OF finite_lessThan, where dflt' = undefined] map_pmf_comp
    by (fastforce simp add: Collect_conj_eq lessThan_def)

  finally show ?thesis .
qed

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

lemma bernoulli_matrix_eq_uncurry_prod :
  fixes m n
  defines \<open>m' \<equiv> {..< m}\<close> and \<open>n' \<equiv> {..< n}\<close>
  shows
    \<open>bernoulli_matrix m n p = (
      prod_pmf m' \<lblot>prod_pmf n' \<lblot>bernoulli_pmf p\<rblot>\<rblot>
        |> map_pmf (\<lambda> \<omega>. \<lambda> (x, y) \<in> m' \<times> n'. \<omega> x y))\<close>
  unfolding bernoulli_matrix_def m'_def n'_def
  by (simp add: prod_pmf_uncurry)

end