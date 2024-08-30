theory Props_Basic

imports
  "HOL-Probability.Product_PMF"
  "HOL-Probability.Hoeffding"
  CVM.Utils_Function
  CVM.Utils_PMF
  CVM.Utils_Real

begin

sledgehammer_params [
  (* verbose = true, *)
  minimize = true,
  preplay_timeout = 30,
  timeout = 70,
  max_facts = smart,
  provers = "
    cvc5 cvc4 z3 verit
    e vampire zipperposition
  "
]

abbreviation eps_del_approxs ("_ \<approx> \<langle> _ , _ \<rangle> _") where "
  f \<approx>\<langle>\<epsilon>, \<delta>\<rangle> x \<equiv> \<P>(\<omega> in measure_pmf f. \<bar>\<omega> - x\<bar> > \<epsilon> * x) \<le> \<delta>"

definition estimate_size :: "nat \<Rightarrow> 'a set \<Rightarrow> nat pmf" where
  [simp] : "
  estimate_size k chi \<equiv> (
    let
      estimate_size_with :: ('a \<Rightarrow> bool) \<Rightarrow> nat = \<lambda> keep_in_chi.
        let chi = Set.filter keep_in_chi chi
        in card chi * 2 ^ k;

      keep_in_chi :: ('a \<Rightarrow> bool) pmf =
        Pi_pmf chi undefined <| \<lambda> _. bernoulli_pmf (1 / 2 ^ k)

    in map_pmf estimate_size_with keep_in_chi)"

lemma estimate_size_empty [simp] :
  "estimate_size k {} = return_pmf 0"
  by auto

lemma estimate_size_approx_correct :
  fixes
    \<epsilon> \<delta> :: real and
    k :: nat and
    chi :: "'a set"
  assumes "
    \<epsilon> > 0" and "
    \<delta> \<ge> 2 * exp (-2 * \<epsilon> ^ 2 / 2 ^ (2 * k))" and "
    finite chi"
  shows "
    (map_pmf real <| estimate_size k chi) \<approx>\<langle>\<epsilon>, \<delta>\<rangle> (card chi)"
proof -
  (*
  Sledgehammer struggled hard with this.
  After some failed runs and fiddling with some params, like increasing the
  preplay_timeout, I (Joe) got a lucky run where it succeeded.

  Intuitively, the idea here is that we may assume wlog that chi is nonempty,
  because if chi were empty, then by the "estimate_size_empty" lemma, the
  function is simply the 0 distribution, and so we always get the exact,
  correct solution when we sample from it.
  *)
  show ?thesis when "card chi > 0 \<Longrightarrow> ?thesis"
    by (smt (z3) app_def assms(2) assms(3) card.empty card_gt_0_iff estimate_size_empty exp_gt_zero id_apply indicator_simps(2) map_return_pmf measure_return_pmf mem_Collect_eq mult_eq_0_iff of_nat_0 that) 

  then show "card chi > 0 \<Longrightarrow> ?thesis"
  proof -
    assume "card chi > 0"

    let ?chi_size_est = "estimate_size k chi"
    let ?binom_prob = "(1 :: real) / 2 ^ k"
    let ?binom = "binomial_pmf (card chi) ?binom_prob"
    let ?binom_mean = "card chi * ?binom_prob"
    let ?two_k_times_binom = "?binom |> map_pmf (\<lambda> x. 2 ^ k * x)"

    have "?chi_size_est = ?two_k_times_binom"
    proof -
      have "\<And> x. pmf ?chi_size_est x = pmf ?two_k_times_binom x"
        sorry
      then show ?thesis using pmf_eqI by blast
    qed

    (*
    Intuitively, the idea here is to:
    1. Use the monotonocity of `?chi_size_est` viewed as a measure, say \<mu>, to
       upper bound `\<mu>({... | ... > ...}) \<le> \<mu>({... | ... \<ge> ...})`
    2. Simplify using the fact that `?chi_size_est` and `?binom` induce the
       same prob measure modulo a factor of `2 ^ k`

    Sledgehammer and auto couldn't prove this one.
    I (Joe) figured that auto could rewrite / simplify away most of the proof,
    but the hard part was probably that it didn't know it needed to use a
    monotonicity argument to prove (1).
    After some digging around the HOL PMF theory file, I noticed a number of
    proofs manually specifying `measure_pmf.finite_measure_mono` as an intro
    pattern to auto, presumably because they faced the same issues with auto.
    *)
    then have "
      \<P>(\<omega> in ?chi_size_est. \<bar>(\<omega> :: real) - card chi\<bar> > \<epsilon> * card chi)
      \<le> \<P>(\<omega> in ?binom. \<bar>2 ^ k * (\<omega> :: real) - card chi\<bar> \<ge> \<epsilon> * card chi)"
      by (auto intro!: measure_pmf.finite_measure_mono)

    (*
    The idea here is that both probabilities are equal, because the arithmetic
    formula in the second probability is obtained by dividing that of the first
    by `2 ^ k`.
       are (extensionally) equal.
    All tactics (including Sledgehammer) struggled with this and my (Joe)
    suspicion is that they weren't aware that:
    1. I wanted to divide by `2 ^ k` on both sides, and
    2. We can safely pull the division into the absolute value.
    Consequently, I manually proved * first, and then performed a `subst` with
    it, and Sledgehammer succeeded thereafter.
    *)
    also have "
      ... = \<P>(\<omega> in ?binom. \<bar>(\<omega> :: real) - ?binom_mean\<bar> \<ge> \<epsilon> * ?binom_mean)"
    proof -
      have * : "\<And> x y. \<bar>x\<bar> \<ge> y \<longleftrightarrow> \<bar>?binom_prob * x\<bar> \<ge> ?binom_prob * y"
        by (smt (verit, del_insts) divide_pos_pos mult_le_cancel_left_pos mult_minus_right zero_less_power)
      then show ?thesis by (subst *, simp add: diff_divide_distrib)
    qed

    (*
    Sledgehammer struggled hard to prove this.
    I (Joe) needed to manually:
    1. Identify the appropriate Hoeffding inequality, namely
       `binomial_distribution.prob_abs_ge`, and explicitly pass it in. 
    2. Simplify the expressions to obtain a format for which the provers
       Sledgehammer called could apply the above inequality.
       This was tricky because simp was too eager, so that I had to undo a
       simplification via `subst *`.
    Therafter, a lucky Sledgehammer run with increased timeouts succeeded.
    *)
    also have "... \<le> 2 * exp (-2 * (\<epsilon> * ?binom_mean) ^ 2 / card chi)"
    proof -
      have * : "card chi / 2 ^ k = card chi * ?binom_prob" by simp
      then show ?thesis
        using binomial_distribution.prob_abs_ge
        by (simp, subst *, metis \<open>0 < card chi\<close> assms(1) atLeastAtMost_iff binomial_distribution.intro divide_le_eq_1_pos divide_pos_pos less_eq_real_def mult_pos_pos of_nat_0_less_iff power_eq_0_iff two_realpow_ge_one zero_le_divide_1_iff zero_le_numeral zero_le_power zero_neq_numeral)
    qed

    also have "... = 2 * exp (-2 * \<epsilon> ^ 2 * ?binom_mean ^ 2 / card chi)"
      by (metis ab_semigroup_mult_class.mult_ac(1) power_mult_distrib)
    also have "... = 2 * exp (-2 * \<epsilon> ^ 2 * card chi / 2 ^ (2 * k))"
      by (simp add: power2_eq_square power_even_eq)
    also have "... \<le> 2 * exp (-2 * \<epsilon> ^ 2 / 2 ^ (2 * k))"
      using \<open>0 < card chi\<close> assms(1) divide_le_cancel by fastforce

    finally show ?thesis using assms by simp
  qed
qed

end