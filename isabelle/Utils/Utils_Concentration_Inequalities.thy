theory Utils_Concentration_Inequalities

imports
  "HOL-Probability.Hoeffding"
  Concentration_Inequalities.Bennett_Inequality
  CVM.Utils_PMF_Bernoulli_Binomial

begin

context prob_space
begin

context
  fixes t B :: real and X :: \<open>'b \<Rightarrow> 'a \<Rightarrow> real\<close> and I
  assumes I : \<open>finite I\<close>
  assumes ind : \<open>indep_vars \<lblot>borel\<rblot> X I\<close>
  assumes intsq : \<open>\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. (X i x)\<^sup>2)\<close>
  assumes t : \<open>t \<ge> 0\<close>
  assumes B : \<open>B > 0\<close>
begin

abbreviation (input) \<open>sum_mean_deviation Y x \<equiv> (\<Sum> i \<in> I. Y i x - expectation (Y i))\<close>

abbreviation \<open>V \<equiv> (\<Sum>i \<in> I. expectation (\<lambda>x. (X i x)\<^sup>2))\<close>

abbreviation (input) "exp_bound \<equiv> exp (- (t\<^sup>2 / (2 * (V + t * B / 3))))"

lemma bernstein_inequality_le :
  assumes bnd: "\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<ge> - B"
  shows \<open>\<P>(x in M. sum_mean_deviation X x \<le> - t) \<le> exp_bound\<close>
proof -
  let ?Y = \<open>\<lambda> i. uminus \<circ> X i\<close>

  note [simp] = comp_def

  have \<open>\<And>i. i \<in> I \<Longrightarrow> AE x in M. ?Y i x \<le> B\<close> using bnd by fastforce 

  moreover have
    \<open>(sum_mean_deviation X x \<le> -t) \<longleftrightarrow> (sum_mean_deviation ?Y x \<ge> t)\<close> for x
    apply simp
    by (metis (mono_tags, lifting) minus_diff_eq more_arith_simps(1) sum.cong sum_negf)

  ultimately show ?thesis
    using
      bernstein_inequality[OF I, where X = ?Y, where t = t, where B = B]
      ind intsq bnd B t
    by (fastforce intro!: indep_vars_compose)
qed

lemma bernstein_inequality_abs_ge :
  assumes \<open>\<And>i. i \<in> I \<Longrightarrow> AE x in M. \<bar>X i x\<bar> \<le> B\<close>
  shows \<open>\<P>(x in M. \<bar>sum_mean_deviation X x\<bar> \<ge> t) \<le> 2 * exp_bound\<close>
proof -
  have
    \<open>{x \<in> space M. \<bar>sum_mean_deviation X x\<bar> \<ge> t} =
      {x \<in> space M. sum_mean_deviation X x \<le> -t} \<union>
      {x \<in> space M. sum_mean_deviation X x \<ge> t}\<close> by auto

  moreover have \<open>\<P>(x in M. sum_mean_deviation X x \<le> -t) \<le> exp_bound\<close>
    using assms bernstein_inequality_le by fastforce

  moreover have \<open>\<P>(x in M. sum_mean_deviation X x \<ge> t) \<le> exp_bound\<close>
    using 
      bernstein_inequality[OF I, where X = X, where t = t, where B = B]
      ind intsq assms B t
    by fastforce

  moreover have
    \<open>{x \<in> space M. sum_mean_deviation X x \<le> -t} \<in> events\<close>
    \<open>{x \<in> space M. sum_mean_deviation X x \<ge> t} \<in> events\<close>
    using ind[unfolded indep_vars_def] by (measurable, auto)+

  ultimately show ?thesis by (smt (verit) finite_measure_subadditive)
qed

end

end

context binomial_distribution
begin

lemma expectation_Pi_bernoulli_nat_pmf_slice :
  assumes \<open>i < n\<close>
  shows
    \<open>measure_pmf.expectation Pi_bernoulli_nat_pmf (flip (<|) i) = p\<close>
    \<open>measure_pmf.expectation Pi_bernoulli_nat_pmf (\<lambda> P. (real <| P i)\<^sup>2) = p\<close>
  using p assms by (
    subst expectation_Pi_pmf_slice,
    auto intro: integrable_measure_pmf_finite)+

lemma integrable_Pi_bernoulli_nat_pmf_square :
  assumes \<open>i < n\<close>
  shows \<open>integrable Pi_bernoulli_nat_pmf <| \<lambda> P. real ((P i)\<^sup>2)\<close>
  using assms
  by (auto
      intro: integrable_Pi_pmf_slice
      simp add: integrable_measure_pmf_finite)

lemma indep_vars_Pi_bernoulli_nat_pmf :
  \<open>prob_space.indep_vars
    Pi_bernoulli_nat_pmf \<lblot>borel\<rblot>
    (\<lambda> i P. real (P i)) {..< n}\<close>
  by (auto
    intro: indep_vars_restrict_intro'
    simp add: restrict_dfl_def)

lemma AE_Pi_bernoulli_nat_pmf_bounded :
  \<open>AE P in Pi_bernoulli_nat_pmf. \<bar>real <| P i\<bar> \<le> 1\<close>
proof (rule AE_pmfI)
  fix P assume \<open>P \<in> set_pmf Pi_bernoulli_nat_pmf\<close>

  then have \<open>P i = 0 \<or> P i = 1\<close>
    by (fastforce simp add: set_Pi_pmf PiE_dflt_def)

  then show \<open>\<bar>real <| P i\<bar> \<le> 1\<close> by auto
qed

lemmas benett_bernstein_inequality_assms =
  expectation_Pi_bernoulli_nat_pmf_slice
  integrable_Pi_bernoulli_nat_pmf_square
  indep_vars_Pi_bernoulli_nat_pmf
  AE_Pi_bernoulli_nat_pmf_bounded

context
  fixes \<delta> :: real
  assumes \<open>n > 0\<close> and \<open>\<delta> \<ge> 0\<close>
begin

text
  \<open>Stronger form of the multiplicative Chernoff bound for the
  Binomial distribution, derived from the Bennet-Bernstein inequality.\<close>
lemma
  defines [simp] : \<open>exponent \<equiv> - real n * p * \<delta>\<^sup>2 / (2 + 2 * \<delta> / 3)\<close>
  shows
    chernoff_prob_ge :
      \<open>\<P>(x in binomial_pmf n p. real x \<ge> real n * p * (1 + \<delta>)) \<le> exp exponent\<close>
      (is \<open>?L_ge \<le> ?R_ge\<close>) and
    chernoff_prob_le :
      \<open>\<P>(x in binomial_pmf n p. real x \<le> real n * p * (1 - \<delta>)) \<le> exp exponent\<close>
      (is \<open>?L_le \<le> ?R_le\<close>) and
    chernoff_abs_ge :
      \<open>\<P>(x in binomial_pmf n p. \<bar>real x - real n * p\<bar> \<ge> real n * p * \<delta>)
      \<le> 2 * exp exponent\<close>
      (is \<open>?L_abs_ge \<le> ?R_abs_ge\<close>)
proof -
  have
    \<open>?L_ge =
      \<P>(P in Pi_bernoulli_nat_pmf.
        (\<Sum> i < n. real (P i) - p) \<ge> real n * p * \<delta>)\<close>
    \<open>?L_le =
      \<P>(P in Pi_bernoulli_nat_pmf.
        (\<Sum> i < n. real (P i) - p) \<le> - real n * p * \<delta>)\<close>
    \<open>?L_abs_ge =
      \<P>(P in Pi_bernoulli_nat_pmf.
        \<bar>\<Sum> i < n. real (P i) - p\<bar> \<ge> real n * p * \<delta>)\<close>
    using p
    by (simp_all add:
      binomial_pmf_eq_map_sum_of_bernoullis
      sum_subtractf field_simps)

  moreover note
    measure_pmf.bernstein_inequality[
      where I = \<open>{..< n}\<close>,
      where M = Pi_bernoulli_nat_pmf,
      where X = \<open>\<lambda> i P. real (P i)\<close>,
      where t = \<open>n * p * \<delta>\<close>, where B = 1]

    measure_pmf.bernstein_inequality_le[
      where I = \<open>{..< n}\<close>,
      where M = Pi_bernoulli_nat_pmf,
      where X = \<open>\<lambda> i P. real (P i)\<close>,
      where t = \<open>n * p * \<delta>\<close>, where B = 1]

    measure_pmf.bernstein_inequality_abs_ge[
      where I = \<open>{..< n}\<close>,
      where M = Pi_bernoulli_nat_pmf,
      where X = \<open>\<lambda> i P. real (P i)\<close>,
      where t = \<open>n * p * \<delta>\<close>, where B = 1]

    benett_bernstein_inequality_assms

  moreover have
    \<open>- (3 * (\<delta>\<^sup>2 * (p\<^sup>2 * (real n)\<^sup>2)) / (p * (real n * 6) + \<delta> * (p * (real n * 2))))
    = exponent\<close>
    using p \<open>n > 0\<close> \<open>\<delta> \<ge> 0\<close>
    apply (simp add: field_split_simps power2_eq_square)
    using arithmetic_simps(63)[of "of_nat n"] add_mono_thms_linordered_field(3)[of "p * (real n * 6) + \<delta> * (p * (real n * 2))" "p * (real n * 6)" "0" "\<delta> * (p * (real n * 2))"]
    by fastforce

  ultimately show \<open>?L_ge \<le> ?R_ge\<close> \<open>?L_le \<le> ?R_le\<close> \<open>?L_abs_ge \<le> ?R_abs_ge\<close>
    using p \<open>n > 0\<close> \<open>\<delta> \<ge> 0\<close> by (auto simp add: field_simps)
qed

end

end

end