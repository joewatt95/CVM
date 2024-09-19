theory Final_Props

imports
  HOL.Power
  "HOL-Probability.Product_PMF"
  "HOL-Probability.Hoeffding"
  CVM.Final_Algo
  CVM.Utils_Approx_Algo
  CVM.Utils_Function
  CVM.Utils_PMF
  CVM.Utils_Real

begin

context
  fixes
    \<epsilon> \<delta> :: real and
    k :: nat and
    chi :: \<open>'a set\<close>
  assumes
    finite_chi : \<open>finite chi\<close>
begin

lemma estimate_distinct_empty :
  \<open>estimate_distinct k {} = return_pmf 0\<close>
  by (auto simp add: estimate_distinct_def)

(*
This shows that`?chi_size_est` is the same distribution as `?binom`, modulo a
factor of `2 ^ k`.

The key observations and steps are:
1. We first use `binomial_pmf_altdef'` to rewrite a `binomial_pmf` into a
  `Pi_pmf` of bernoullis.
    This puts `?binom` into a similar form as `?chi_size_est`, on which we
    can perform more simplifications.
2. Finish the proof via a congruence property of `map_pmf` via
  `map_pmf_cong` and routine simplifications, using the functor laws
  via `map_pmf_comp` to squish multiple `map_pmf` into one.
*)
lemma estimate_distinct_eq_binomial :
  defines \<open>binom \<equiv> binomial_pmf (card chi) ((1 :: real) / 2 ^ k)\<close>
  shows \<open>estimate_distinct k chi = map_pmf ((*) <| 2 ^ k) binom\<close>

  apply (simp only: estimate_distinct_def binom_def)
  apply (subst binomial_pmf_altdef')
  by (auto
      intro!: map_pmf_cong
      simp add: map_pmf_comp Set.filter_def finite_chi)

lemma estimate_distinct_approx_correct :
  assumes \<open>\<epsilon> > 0\<close>
  defines \<open>\<delta> \<equiv> 2 * exp (-2 * \<epsilon>\<^sup>2 * card chi / 2 ^ (2 * k))\<close>
  shows \<open>(estimate_distinct k chi) \<approx>\<langle>\<epsilon>, \<delta>\<rangle> (card chi)\<close>
proof -
  (*
  First, we may assume wlog that chi is nonempty, because if chi were empty,
  then `estimate_distinct_empty` is the key result that says the function is simply
  the 0 distribution, and so we always get the exact, correct solution when we
  sample from it.

  To get this to work, I (Joe) had to:
  1. Increase timeouts: sledgehammer[timeout = 60, preplay_timeout = 10]
  2. Explicitly pass in the key `estimate_distinct_empty` lemma, and `that`. 
  *)
  show ?thesis when \<open>card chi > 0 \<Longrightarrow> ?thesis\<close>
    using estimate_distinct_empty finite_chi assms that
    by (smt (verit, best) card_0_eq exp_gt_zero gr_zeroI indicator_simps(2) measure_return_pmf mem_Collect_eq mult_not_zero of_nat_0)

  then show \<open>card chi > 0 \<Longrightarrow> ?thesis\<close>
  proof -
    assume \<open>card chi > 0\<close>

    let ?chi_size_est = \<open>estimate_distinct k chi\<close>
    let ?binom_prob = \<open>(1 :: real) / 2 ^ k\<close>
    let ?binom = \<open>binomial_pmf (card chi) ?binom_prob\<close>
    let ?binom_mean = \<open>card chi * ?binom_prob\<close>

    (*
    We bound the probability of `?chi_size_est` with that of `?binom`.
    Intuitively, the idea here is to:
    1. Use the monotonocity of `?chi_size_est` (viewed as a measure) with
       the fact that `x > y \<longrightarrow> x \<ge> y`.
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
    have
      \<open>\<P>(\<omega> in ?chi_size_est. \<bar>(\<omega> :: real) - card chi\<bar> > \<epsilon> * card chi)
        \<le> \<P>(\<omega> in ?binom. \<bar>2 ^ k * (\<omega> :: real) - card chi\<bar> \<ge> \<epsilon> * card chi)\<close>
      unfolding estimate_distinct_eq_binomial
      by (auto intro!: measure_pmf.finite_measure_mono)

    (*
    We then transform the expression into a form that's more suitable for
    the Hoeffding inequality `binomial_distribution.prob_abs_ge` in the HOL
    probability lib.

    The idea here is that both probabilities are equal, because the arithmetic
    formula in the second probability is obtained by dividing that of the first
    by `2 ^ k`.

    All tactics (including sledgehammer) struggled with this and my (Joe)
    suspicion is that they weren't aware that:
    1. I wanted to divide by `2 ^ k` on both sides, and
    2. We can safely pull the division into the absolute value.
    Consequently, I manually proved * first, and then performed a `subst` with
    it, and Sledgehammer succeeded thereafter.
    *)
    also have
      \<open>... = \<P>(\<omega> in ?binom. \<bar>(\<omega> :: real) - ?binom_mean\<bar> \<ge> \<epsilon> * ?binom_mean)\<close>
    proof -
      have * : \<open>\<And> x y. \<bar>x\<bar> \<ge> y \<equiv> \<bar>?binom_prob * x\<bar> \<ge> ?binom_prob * y\<close>
        by (simp add: divide_le_cancel)
      show ?thesis by (subst *, simp add: diff_divide_distrib)
    qed

    (*
    Next, we apply Hoeffding's inequality for binomials.

    It was difficult to get sledgehammer to prove this.
    I (Joe) needed to manually:
    1. Identify the appropriate Hoeffding inequality, namely
       `binomial_distribution.prob_abs_ge`, and explicitly pass it in. 
    2. Simplify the expressions to obtain a form for which the provers
       sledgehammer called could apply the above inequality.
       This was tricky because simp was too eager, so that I had to first prove 
       an equality which undoes a simplification, and then run sledgehammer.
    3. Increase timeouts and limit max_facts:
       sledgehammer [max_facts = 100, timeout = 120, preplay_timeout = 60]
    *)
    also have \<open>... \<le> 2 * exp (-2 * (\<epsilon> * ?binom_mean)\<^sup>2 / card chi)\<close>
    proof -
      have \<open>card chi / 2 ^ k = card chi * ?binom_prob\<close> by simp
      then show ?thesis
        using binomial_distribution.prob_abs_ge assms
        by (simp, metis \<open>card chi > 0\<close> atLeastAtMost_iff binomial_distribution.intro divide_le_eq_1_pos divide_pos_pos less_eq_real_def mult_pos_pos of_nat_0_less_iff two_realpow_ge_one zero_le_divide_1_iff zero_less_numeral zero_less_power)
    qed

    (* Finally, we do some simplifications and relaxation of the bound. *)
    also have \<open>... = 2 * exp (-2 * \<epsilon>\<^sup>2 * card chi / 2 ^ (2 * k))\<close>
      by (simp add: power2_eq_square power_even_eq)

    (* also have \<open>... \<le> 2 * exp (-2 * \<epsilon> ^ 2 / 2 ^ (2 * k))\<close>
      using assms \<open>0 < card chi\<close> divide_le_cancel by fastforce  *)

    finally show ?thesis using assms by blast
  qed
qed

definition threshold :: real where
  \<open>threshold \<equiv> log2 (2 / \<delta>) / (2 * \<epsilon>\<^sup>2)\<close>

lemma estimate_distinct_approx_correct' :
  assumes
    \<open>\<epsilon> > 0\<close> and
    \<open>\<delta> > 0\<close> and
    \<open>k \<le> (log2 <| card chi / threshold) / 2\<close> (is \<open>_ \<le> ?x\<close>)
  shows "(estimate_distinct k chi) \<approx>\<langle>\<epsilon>, \<delta>\<rangle> (card chi)"
proof -
  show ?thesis when \<open>\<lbrakk>\<delta> \<le> 1; card chi > 0\<rbrakk> \<Longrightarrow> ?thesis\<close>
    using assms finite_chi estimate_distinct_empty
    by (metis (mono_tags, lifting) abs_eq_0 card_gt_0_iff diff_zero indicator_simps(2) landau_o.R_linear less_eq_real_def measure_pmf.subprob_measure_le_1 measure_return_pmf mem_Collect_eq mult_eq_0_iff nat_less_le of_nat_0_eq_iff order_less_irrefl order_trans that zero_le)

  then show \<open>\<lbrakk>\<delta> \<le> 1; card chi > 0\<rbrakk> \<Longrightarrow> ?thesis\<close>
  proof -
    assume \<open>\<delta> \<le> 1\<close> and \<open>card chi > 0\<close>

    let ?\<delta> = \<open>\<lambda> pow. 2 * exp (-2 * \<epsilon>\<^sup>2  * card chi / (2 powr (2 * pow)))\<close>

    have \<open>(estimate_distinct k chi) \<approx>\<langle>\<epsilon>, ?\<delta> k\<rangle> (card chi)\<close>
      using assms estimate_distinct_approx_correct
      apply simp
      by (metis of_nat_numeral power_even_eq powr_power powr_realpow zero_less_numeral zero_neq_numeral)

    then show ?thesis when \<open>?\<delta> k \<le> \<delta>\<close> (is ?thesis)
      using relax_eps_del_approx that by linarith

    show ?thesis
    proof -
      have \<open>?\<delta> k \<le> ?\<delta> ?x\<close>
        using assms by (simp add: field_simps landau_o.R_mult_left_mono)

      also have \<open>... = 2 * exp (- log2 <| 2 / \<delta>)\<close>
        using assms \<open>0 < card chi\<close> \<open>\<delta> \<le> 1\<close> by (simp add: threshold_def)

      also have \<open>... = 2 * exp (log2 <| \<delta> / 2)\<close>
        by (simp add: assms(2) log_divide) 

      also have \<open>... = 2 * (\<delta> / 2) powr log2 (exp 1)\<close>
        by (metis (no_types, opaque_lifting) assms(2) div_by_1 divide_divide_eq_right divide_eq_0_iff ln_exp log_def mult.commute order_less_irrefl powr_def)

      also have \<open>... \<le> \<delta>\<close>
        using \<open>\<delta> \<le> 1\<close>
        by (smt (verit, best) assms(2) divide_minus_left exp_ge_add_one_self one_le_log_cancel_iff powr_le_one_le real_average_minus_first)

      finally show ?thesis by blast
    qed
  qed
qed

end

end