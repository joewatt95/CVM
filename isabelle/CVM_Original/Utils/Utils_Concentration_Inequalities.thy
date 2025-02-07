theory Utils_Concentration_Inequalities

imports
  "HOL-Probability.Hoeffding"
  Concentration_Inequalities.Bennett_Inequality
  Utils_PMF_Basic

begin

locale benett_bernstein = prob_space +
  fixes X :: \<open>'b \<Rightarrow> 'a \<Rightarrow> real\<close> and I
  assumes
    I : \<open>finite I\<close> and
    ind : \<open>indep_vars \<lblot>borel\<rblot> X I\<close> and
    intsq : \<open>\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda> x. (X i x)\<^sup>2)\<close>
begin

abbreviation (input)
  \<open>sum_mean_deviation Y x \<equiv> \<Sum> i \<in> I. Y i x - expectation (Y i)\<close>

abbreviation \<open>V \<equiv> \<Sum> i \<in> I. expectation (\<lambda> x. (X i x)\<^sup>2)\<close>

context
  fixes t B :: real
  assumes t : \<open>t \<ge> 0\<close> and B : \<open>B > 0\<close>
begin

abbreviation (input) \<open>exp_bound \<equiv> exp (- t\<^sup>2 / (2 * (V + t * B / 3)))\<close>

lemma bernstein_inequality_ge :
  assumes \<open>\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<le> B\<close>
  shows \<open>\<P>(x in M. sum_mean_deviation X x \<ge> t) \<le> exp_bound\<close>
  using bernstein_inequality[OF I ind intsq assms(1) t B] by simp

lemma bernstein_inequality_le :
  assumes \<open>\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<ge> - B\<close>
  shows \<open>\<P>(x in M. sum_mean_deviation X x \<le> - t) \<le> exp_bound\<close>
proof -
  let ?Y = \<open>\<lambda> i. uminus \<circ> X i\<close>

  from assms have
    \<open>AE x in M. ?Y i x \<le> B\<close> if \<open>i \<in> I\<close> for i using that by fastforce 

  moreover have
    \<open>(sum_mean_deviation X x \<le> -t) \<longleftrightarrow> (sum_mean_deviation ?Y x \<ge> t)\<close> for x
    by (auto simp add: comp_def sum_subtractf)

  ultimately show ?thesis
    using
      bernstein_inequality[OF I, where X = ?Y and t = t and B = B]
      ind intsq assms B t
    by (force intro!: indep_vars_compose)
qed

lemma bernstein_inequality_abs_ge :
  assumes \<open>\<And> i. i \<in> I \<Longrightarrow> AE x in M. \<bar>X i x\<bar> \<le> B\<close>
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
      bernstein_inequality[OF I, where X = X and t = t and B = B]
      ind intsq assms B t
    by force

  moreover have
    \<open>{x \<in> space M. sum_mean_deviation X x \<le> -t} \<in> events\<close>
    \<open>{x \<in> space M. sum_mean_deviation X x \<ge> t} \<in> events\<close>
    using ind[simplified indep_vars_def] by (measurable, fastforce)+

  ultimately show ?thesis by (smt (verit) finite_measure_subadditive)
qed

end

end

context binomial_distribution
begin

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

lemmas benett_bernstein_inequality_assms =
  integrable_Pi_bernoulli_nat_pmf_square
  indep_vars_Pi_bernoulli_nat_pmf

lemma expectation_Pi_bernoulli_nat_pmf_slice [simp] :
  assumes \<open>i < n\<close>
  shows
    \<open>measure_pmf.expectation Pi_bernoulli_nat_pmf (\<lambda> P. real (P i)) = p\<close>
    \<open>measure_pmf.expectation Pi_bernoulli_nat_pmf (\<lambda> P. (real <| P i)\<^sup>2) = p\<close>
  using p assms
  by (
    subst expectation_Pi_pmf_slice,
    auto intro: integrable_measure_pmf_finite)+

lemma
  defines [simp] : \<open>Q f \<equiv> AE P in Pi_bernoulli_nat_pmf. f P\<close>
  shows
    AE_Pi_bernoulli_nat_pmf_0_1 :
      \<open>Q (\<lambda> P. P i = 0 \<or> P i = 1)\<close> (is ?thesis_0) and
    AE_Pi_bernoulli_nat_pmf_abs_bounded :
      \<open>Q (\<lambda> P. \<bar>real <| P i\<bar> \<le> 1)\<close> (is ?thesis_1)
proof -
  show ?thesis_0
    by (fastforce intro: AE_pmfI simp add: set_Pi_pmf PiE_dflt_def)
  then show ?thesis_1 by fastforce
qed

text
  \<open>Stronger form of the multiplicative Chernoff bounds for the
  Binomial distribution, derived from the Bennet-Bernstein inequality.\<close>

lemma
  assumes \<open>\<delta> \<ge> 0\<close>
  shows
    chernoff_prob_le :
      \<open>\<P>(x in binomial_pmf n p. real x \<le> real n * p * (1 - \<delta>))
      \<le> exp (- real n * p * \<delta>\<^sup>2 / 2)\<close>
      (is \<open>?L_le \<le> ?R_le\<close>) and
    chernoff_prob_ge :
      \<open>\<P>(x in binomial_pmf n p. real x \<ge> real n * p * (1 + \<delta>))
      \<le> exp (- real n * p * \<delta>\<^sup>2 / (2 + 2 * \<delta> / 3))\<close>
      (is \<open>?L_ge \<le> ?R_ge\<close>) and
    chernoff_prob_abs_ge :
      \<open>\<P>(x in binomial_pmf n p. \<bar>real x - real n * p\<bar> \<ge> real n * p * \<delta>)
      \<le> 2 * exp (- real n * p * \<delta>\<^sup>2 / (2 + 2 * \<delta> / 3))\<close>
      (is \<open>?L_abs_ge \<le> ?R_abs_ge\<close>)
proof -
  interpret Pi_bernoulli_nat_pmf :
    benett_bernstein Pi_bernoulli_nat_pmf \<open>\<lambda> i P. real (P i)\<close> \<open>{..< n}\<close> 
    using benett_bernstein_inequality_assms
    by (unfold_locales, auto)

  let ?prob = \<open>\<lambda> R.
    \<P>(P in Pi_bernoulli_nat_pmf. R (\<Sum> i < n. real (P i) - p) (real n * p * \<delta>))\<close>
  let ?t = \<open>n * p * \<delta>\<close>

  have lhs_eq :
    \<open>?L_le = ?prob (\<lambda> sum_mean_deviation np\<delta>. sum_mean_deviation \<le> -np\<delta>)\<close>
    \<open>?L_ge = ?prob (\<ge>)\<close>
    \<open>?L_abs_ge = ?prob (\<lambda> sum_mean_deviation np\<delta>. \<bar>sum_mean_deviation\<bar> \<ge> np\<delta>)\<close>
    by (simp_all add:
      binomial_pmf_eq_map_sum_of_bernoullis sum_subtractf field_simps)

  have arithmetic_aux :
    \<open>(real n * p * \<delta>)\<^sup>2 / (2 * (n * p) + 2 * (n * p * \<delta> * B) / 3)
    = real n * p * \<delta>\<^sup>2 / (2 + 2 * B * \<delta> / 3)\<close> for B
    apply (simp add: field_split_simps power_numeral_reduce)
    apply (simp only: Multiseries_Expansion.intyness_simps)
    by (smt (verit, del_insts) Num.of_nat_simps(5) mult_eq_0_iff nat_distrib(2) of_nat_eq_0_iff vector_space_over_itself.scale_left_commute)
  show \<open>?L_ge \<le> ?R_ge\<close> \<open>?L_abs_ge \<le> ?R_abs_ge\<close>
    using
      lhs_eq arithmetic_aux[of 1] p \<open>\<delta> \<ge> 0\<close>
      Pi_bernoulli_nat_pmf.bernstein_inequality_ge[of ?t 1]
      Pi_bernoulli_nat_pmf.bernstein_inequality_abs_ge[of ?t 1]
      AE_Pi_bernoulli_nat_pmf_abs_bounded
    by simp_all

  have
    \<open>?L_le \<le> exp (- real n * p * \<delta>\<^sup>2 / (2 + 2 * B * \<delta> / 3))\<close>
    (is \<open>_ \<le> ?R_le' B\<close>) if \<open>B > 0\<close> for B
    using
      lhs_eq arithmetic_aux that p \<open>\<delta> \<ge> 0\<close>
      Pi_bernoulli_nat_pmf.bernstein_inequality_le[of ?t B]
    by simp

  moreover have \<open>?R_le' \<midarrow>0\<rightarrow> ?R_le\<close>
    apply (intro tendsto_intros)
    using
      bounded_linear_mult_right[of "2"]
      tendsto_add_const_iff[of "2" "\<lambda> R. 2 * R * \<delta> / 3" "0" "at 0"]
      linear_lim_0[of "(*) 2"] tendsto_mult_left_zero[of "(*) 2" "at 0" \<delta>]
      tendsto_divide_zero[of "\<lambda> R. 2 * R * \<delta>" "at 0" "3"]
    by auto

  ultimately show \<open>?L_le \<le> ?R_le\<close>
    using
      eventually_at_right_less[of "0"]
      eventually_mono[of "(<) 0" "at_right 0" "\<lambda> uuc. measure_pmf.prob (binomial_pmf n p) {uuc. real uuc \<le> real n * p * (1 - \<delta>)} \<le> exp (- (real n * p * \<delta>\<^sup>2 / (2 + 2 * uuc * \<delta> / 3)))"]
    by (fastforce
      intro!: tendsto_lowerbound[of _ ?R_le \<open>at_right 0\<close>]
      simp add: filterlim_at_split)
qed

end

end