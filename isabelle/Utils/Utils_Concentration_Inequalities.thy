theory Utils_Concentration_Inequalities

imports
  "HOL-Probability.Hoeffding"
  Concentration_Inequalities.Bennett_Inequality
  CVM.Utils_PMF_Bernoulli_Binomial

begin

locale benett_bernstein = prob_space +
  fixes X :: \<open>'b \<Rightarrow> 'a \<Rightarrow> real\<close> and I
  assumes I : \<open>finite I\<close>
  assumes ind : \<open>indep_vars \<lblot>borel\<rblot> X I\<close>
  assumes intsq : \<open>\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. (X i x)\<^sup>2)\<close>

begin

abbreviation (input)
  \<open>sum_mean_deviation Y x \<equiv> (\<Sum> i \<in> I. Y i x - expectation (Y i))\<close>

abbreviation \<open>V \<equiv> (\<Sum>i \<in> I. expectation (\<lambda>x. (X i x)\<^sup>2))\<close>

context
  fixes t B :: real
  assumes t : \<open>t \<ge> 0\<close>
  assumes B : \<open>B > 0\<close>
begin

abbreviation (input) "exp_bound \<equiv> exp (- t\<^sup>2 / (2 * (V + t * B / 3)))"

lemma bernstein_inequality_ge :
  assumes bnd: "\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<le> B"
  shows \<open>\<P>(x in M. sum_mean_deviation X x \<ge> t) \<le> exp_bound\<close>
  using bernstein_inequality[OF I ind intsq bnd t B, simplified]
  by argo

lemma bernstein_inequality_le :
  assumes bnd: "\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<ge> - B"
  shows \<open>\<P>(x in M. sum_mean_deviation X x \<le> - t) \<le> exp_bound\<close>
proof -
  let ?Y = \<open>\<lambda> i. uminus \<circ> X i\<close>

  have \<open>\<And>i. i \<in> I \<Longrightarrow> AE x in M. ?Y i x \<le> B\<close> using bnd by fastforce 

  moreover have
    \<open>(sum_mean_deviation X x \<le> -t) \<longleftrightarrow> (sum_mean_deviation ?Y x \<ge> t)\<close> for x
    apply (simp add: comp_def)
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
  using p assms by (
    subst expectation_Pi_pmf_slice,
    auto intro: integrable_measure_pmf_finite)+

lemma
  defines [simp] : \<open>Q f \<equiv> AE P in Pi_bernoulli_nat_pmf. f P\<close>
  shows
    AE_Pi_bernoulli_nat_pmf_0_1 :
      \<open>Q (\<lambda> P. P i = 0 \<or> P i = 1)\<close> (is ?thesis_0) and
    AE_Pi_bernoulli_nat_pmf_abs_bounded :
      \<open>Q (\<lambda> P. \<bar>real <| P i\<bar> \<le> 1)\<close> (is ?thesis_1) and
    AE_Pi_bernoulli_nat_pmf_bounded_from_below :
      \<open>B > 0 \<Longrightarrow> Q (\<lambda> P. real (P i) \<ge> -B)\<close> (is \<open>_ \<Longrightarrow> ?thesis_2\<close>)
proof -
  show ?thesis_0
    by (fastforce intro: AE_pmfI simp add: set_Pi_pmf PiE_dflt_def)
  then show ?thesis_1 by fastforce
  show \<open>B > 0 \<Longrightarrow> ?thesis_2\<close> by simp
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
  let ?t = \<open>real n * p * \<delta>\<close>

  have lhs_eq :
    \<open>?L_le = ?prob (\<lambda> sum_mean_deviation np\<delta>. sum_mean_deviation \<le> -np\<delta>)\<close>
    \<open>?L_ge = ?prob (\<lambda> sum_mean_deviation np\<delta>. sum_mean_deviation \<ge> np\<delta>)\<close>
    \<open>?L_abs_ge = ?prob (\<lambda> sum_mean_deviation np\<delta>. \<bar>sum_mean_deviation\<bar> \<ge> np\<delta>)\<close>
    by (simp_all add:
      binomial_pmf_eq_map_sum_of_bernoullis sum_subtractf field_simps)

  moreover note
    Pi_bernoulli_nat_pmf.bernstein_inequality_ge[of ?t 1]
    Pi_bernoulli_nat_pmf.bernstein_inequality_abs_ge[of ?t 1]
    AE_Pi_bernoulli_nat_pmf_abs_bounded

  moreover have
    \<open>3 * (\<delta>\<^sup>2 * (p\<^sup>2 * (real n)\<^sup>2)) / (p * (real n * 6) + \<delta> * (p * (real n * 2)))
    = real n * p * \<delta>\<^sup>2 / (2 + 2 * \<delta> / 3)\<close>
    apply (simp add: field_split_simps power2_eq_square)
    by (metis of_nat_0_eq_iff[of n] Groups.mult_ac(3)[of "real n * (6 + \<delta> * 2)" "real n" "6 + \<delta> * 2"] Groups.mult_ac(3)[of p "real n" "real n * (6 + \<delta> * 2) * (6 + \<delta> * 2)"]
      Groups.mult_ac(3)[of "real n * (6 + \<delta> * 2)" p "6 + \<delta> * 2"] Groups.mult_ac(3)[of "real n" "real n * (6 + \<delta> * 2)" "p * (6 + \<delta> * 2)"] Groups.mult_ac(3)[of \<delta> p "2"]
      Groups.mult_ac(3)[of p "real n" "6"] Groups.mult_ac(3)[of "real n" \<delta> "p * 2"] Groups.mult_ac(3)[of "real n" p "2"] nat_distrib(2)[of p "6" "\<delta> * 2"]
      nat_distrib(2)[of "real n" "p * 6" "\<delta> * (p * 2)"] mult_eq_0_iff[of "real n" "6 + \<delta> * 2"] mult_eq_0_iff[of "real n * (6 + \<delta> * 2)" "real n * (6 + \<delta> * 2)"]
      mult_eq_0_iff[of p "real n * (real n * (6 + \<delta> * 2) * (6 + \<delta> * 2))"] mult_eq_0_iff[of "real n * (6 + \<delta> * 2)" "0"])

  ultimately show \<open>?L_ge \<le> ?R_ge\<close> \<open>?L_abs_ge \<le> ?R_abs_ge\<close>
    using p assms by (simp_all add: field_simps)

  have
    \<open>3 * (\<delta>\<^sup>2 * (p\<^sup>2 * (real n)\<^sup>2)) / (p * (real n * 6) + B * (\<delta> * (p * (real n * 2))))
    = p * (real n * (3 * \<delta>\<^sup>2)) / (6 + B * (\<delta> * 2))\<close> for B
    apply (simp add: field_split_simps power2_eq_square)
    by (metis mult.commute[of "real n * p" "real n"] mult.commute[of "0" p] mult.commute[of "B * \<delta>" "real n"] mult.commute[of "B * \<delta>" p]
      nat_distrib(2)[of "real n" "6" "B * (\<delta> * 2)"] nat_distrib(2)[of p "real n * 6" "B * (\<delta> * (real n * 2))"] of_nat_eq_0_iff[of n] mult_eq_0_iff[of "of_nat n" "of_nat n"]
      mult_eq_0_iff[of "real n * real n" p] mult_eq_0_iff[of "real n * (p * real n)" "6 + B * (\<delta> * 2)"] mult_eq_0_iff[of "of_nat n" "0"] mult_eq_0_iff[of "0" p]
      ab_semigroup_mult_class.mult_ac(1)[of "real n" "real n" p] ab_semigroup_mult_class.mult_ac(1)[of "real n" p "real n"]
      ab_semigroup_mult_class.mult_ac(1)[of "real n" "p * real n" "6 + B * (\<delta> * 2)"] ab_semigroup_mult_class.mult_ac(1)[of p "real n" "6 + B * (\<delta> * 2)"]
      ab_semigroup_mult_class.mult_ac(1)[of "real n" "B * \<delta>" "2"] ab_semigroup_mult_class.mult_ac(1)[of "B * \<delta>" "real n" "2"] ab_semigroup_mult_class.mult_ac(1)[of B \<delta> "2"]
      ab_semigroup_mult_class.mult_ac(1)[of B \<delta> "p * (real n * 2)"] ab_semigroup_mult_class.mult_ac(1)[of p "B * \<delta>" "real n * 2"]
      ab_semigroup_mult_class.mult_ac(1)[of "B * \<delta>" p "real n * 2"] ab_semigroup_mult_class.mult_ac(1)[of B \<delta> "real n * 2"])

  then have
    \<open>?L_le \<le> exp (- real n * p * \<delta>\<^sup>2 / (2 + 2 * B * \<delta> / 3))\<close>
    (is \<open>_ \<le> ?R_le' B\<close>) if \<open>B > 0\<close> for B
    using
      lhs_eq Pi_bernoulli_nat_pmf.bernstein_inequality_le[of ?t B]
      that p \<open>\<delta> \<ge> 0\<close> 
    by (simp add: field_simps)

  moreover have \<open>?R_le' \<midarrow>0\<rightarrow> ?R_le\<close>
    using
      bounded_linear_mult_right[of "2"]
      tendsto_add_const_iff[of "2" "\<lambda> R. 2 * R * \<delta> / 3" "0" "at 0"]
      linear_lim_0[of "(*) 2"] tendsto_mult_left_zero[of "(*) 2" "at 0" \<delta>]
      tendsto_divide_zero[of "\<lambda> R. 2 * R * \<delta>" "at 0" "3"]
    by (auto intro!: tendsto_intros)

  ultimately show \<open>?L_le \<le> ?R_le\<close>
    using
      eventually_at_right_less[of "0"]
      eventually_mono[of "(<) 0" "at_right 0" "\<lambda>uuc. measure_pmf.prob (binomial_pmf n p) {uuc. real uuc \<le> real n * p * (1 - \<delta>)} \<le> exp (- (real n * p * \<delta>\<^sup>2 / (2 + 2 * uuc * \<delta> / 3)))"]
    by (fastforce
      intro!: tendsto_lowerbound[of _ ?R_le \<open>at_right 0\<close>]
      simp add: filterlim_at_split)
qed

end

end