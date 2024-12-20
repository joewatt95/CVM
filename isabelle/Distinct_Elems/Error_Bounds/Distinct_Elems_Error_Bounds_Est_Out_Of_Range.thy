theory Distinct_Elems_Error_Bounds_Est_Out_Of_Range

imports
  "HOL-Library.Sum_of_Squares"
  CVM.Distinct_Elems_Error_Bounds_Common
  CVM.Distinct_Elems_Algo_Transforms_No_Fail
  CVM.Distinct_Elems_Algo_Transforms_Eager
  CVM.Distinct_Elems_Algo_Transforms_Binomial
  CVM.Utils_Compat_Discrete
  CVM.Utils_Real
  CVM.Utils_Concentration_Inequalities

begin

definition (in with_threshold_r_l_\<epsilon>_xs)
  \<open>prob_k_le_l_and_est_out_of_range_bound \<equiv>
    4 * exp (-\<epsilon>\<^sup>2 * threshold / (4 * real r * (1 + \<epsilon> / 3)))\<close>

context with_threshold_pos_r_l_\<epsilon>_xs
begin

context
  assumes
    \<open>threshold \<ge> r\<close>
    \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close>
begin

lemma l_le_length_xs :
  \<open>l \<le> length xs\<close>
proof -
  from \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close>
  have \<open>l \<le> Utils_Compat_Discrete.floor_log (2 * r * card (set xs) div threshold)\<close>
    by (metis Utils_Compat_Discrete.floor_log_le_iff less_eq_div_iff_mult_less_eq Utils_Compat_Discrete.floor_log_power threshold_pos)

  also have \<open>\<dots> \<le> Utils_Compat_Discrete.floor_log (2 * length xs)\<close>
    apply (rule Utils_Compat_Discrete.floor_log_le_iff)
    using \<open>threshold \<ge> r\<close>
    by (smt (verit, best) card_length div_le_mono le_trans less_eq_nat.simps(1) mult.commute mult.left_commute mult_le_mono1 nonzero_mult_div_cancel_right
      semidom_div_by_0)

  also have \<open>\<dots> \<le> length xs\<close>
    by (metis Utils_Compat_Discrete.floor_log_le_iff less_exp Utils_Compat_Discrete.floor_log_exp2_le Utils_Compat_Discrete.floor_log_power Utils_Compat_Discrete.floor_log_twice nat_0_less_mult_iff not_le not_less_eq_eq order_class.order_eq_iff self_le_ge2_pow zero_le)

  finally show ?thesis .
qed

lemma r_pos :
  \<open>r > 0\<close>
  using
    \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close>
    threshold_pos power_eq_0_iff
  by fastforce

theorem prob_eager_algo_k_le_l_and_est_out_of_range_le :
  assumes \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close>
  shows
    \<open>\<P>(state in run_with_bernoulli_matrix <| run_reader <<< eager_algorithm.
      state_k state \<le> l \<and>
      real (compute_estimate state) >[\<epsilon>] card (set xs))
    \<le> prob_k_le_l_and_est_out_of_range_bound\<close>
    (is \<open>?L (\<le>) l \<le> _\<close>)
proof (cases xs)
  case Nil
  then show ?thesis
    using \<open>\<epsilon> > 0\<close>
    by (simp add:
      eager_algo_simps eager_algorithm_def compute_estimate_def
      prob_k_le_l_and_est_out_of_range_bound_def)
next
  let ?exp_bound =
    \<open>exp (-\<epsilon>\<^sup>2 * threshold / (4 * real r * (1 + \<epsilon> / 3)))\<close>
  let ?exp_term = \<open>\<lambda> k.
    exp (- real (card <| set xs) * \<epsilon>\<^sup>2 / (2 ^ k * (2 + 2 * \<epsilon> / 3)))\<close>

  case (Cons _ _)
  then have \<open>?exp_term k < 1\<close> for k
    using \<open>\<epsilon> > 0\<close>
    by (simp add: field_split_simps add_strict_increasing2 card_gt_0_iff)

  let ?binom_mean = \<open>\<lambda> k. real (card <| set xs) / 2 ^ k\<close>

  text \<open>Apply subadditivity.\<close>
  have \<open>?L (\<le>) l \<le> (\<Sum> k \<le> l. ?L (=) k)\<close>
  proof -
    have [simp] :
      \<open>{x. f x \<le> l \<and> P x} = (
        \<Union> k \<le> l. {x. f x = k \<and> P x})\<close> for f :: \<open>'b \<Rightarrow> nat\<close> and P by auto

    show ?thesis
      by (auto
        intro: measure_pmf.finite_measure_subadditive_finite
        simp add: vimage_def)
  qed

  text \<open>Transform to nondeterministic algorithm.\<close>
  also have \<open>\<dots> \<le> (
    \<Sum> k \<le> l.
      \<P>(estimate in run_with_bernoulli_matrix <| nondet_alg k.
        2 ^ k * real estimate >[\<epsilon>] real (card <| set xs)))\<close>
    by (auto
      intro: sum_mono pmf_mono
      simp add:
        nondet_alg_def compute_estimate_def algebra_simps
        eager_algorithm_inv[unfolded eager_state_inv_def])

  text \<open>Transform to binomial distribution and weaken > to >=.\<close>
  also have \<open>\<dots> \<le> (
    \<Sum> k \<le> l.
      \<P>(estimate in binomial_pmf (card <| set xs) <| 1 / 2 ^ k.
        \<bar>real estimate - ?binom_mean k\<bar> \<ge> \<epsilon> * ?binom_mean k))\<close>
    (is \<open>_ \<le> (\<Sum> k \<le> _. ?L k)\<close>)
    using \<open>\<epsilon> > 0\<close> l_le_length_xs 
    by (auto
      intro!: sum_mono intro: pmf_mono
      simp add:
        map_pmf_nondet_alg_eq_binomial[
          where m = \<open>length xs\<close>, where n = \<open>length xs\<close>, symmetric]
        field_simps)

  text \<open>Apply Chernoff bound to each term.\<close>
  also have \<open>\<dots> \<le> (\<Sum> k \<le> l. 2 * ?exp_term k)\<close> (is \<open>_ \<le> (\<Sum> k \<le> _. ?R k)\<close>)
  proof (rule sum_mono)
    fix k
    from
      binomial_distribution.chernoff_prob_abs_ge[
        where n = \<open>card <| set xs\<close>, where p = \<open>1 / 2 ^ k\<close>, where \<delta> = \<epsilon>,
        simplified binomial_distribution_def]
      \<open>\<epsilon> > 0\<close>
    show \<open>?L k \<le> ?R k\<close> by (simp add: field_simps)
  qed

  text
    \<open>In preparation to bound via a geometric series, we first transform each
    term to be of the form `2 * exp_term l * 2 ^ r` so that we can later pull
    out a factor of `2 * exp_term l` from each term.
    Note that `exp_term l < 1` and that this is important for obtaining a tight
    bound later on.\<close>
  also have
    \<open>\<dots> = (\<Sum> k \<le> l. 2 * ?exp_term l ^ 2 ^ (l - k))\<close> (is \<open>_ = sum ?g _\<close>)
    apply (rule sum.cong[OF refl])
    using \<open>\<epsilon> > 0\<close>
    apply (simp add:
      exp_of_nat_mult[symmetric] power_add[symmetric] field_split_simps)
    by (smt (verit, best) mult_sign_intros(5) one_le_power)

  text
    \<open>Now we do the following:
    1. Reverse the summation from `l --> 0`, to `0 --> l`
    2. Reindex the sum to be taken over exponents `r` of the form `2 ^ k`
       instead of being over all `k`.
    3. Pull out a factor of `2 * exp_term l` from each term.\<close>
  also have
    \<open>\<dots> = 2 * ?exp_term l * (\<Sum> r \<in> power 2 ` {.. l}. ?exp_term l ^ (r - 1))\<close>
    using
      sum.atLeastAtMost_rev[of ?g 0 l, simplified atLeast0AtMost]
      power_add[of "?exp_term l" "1" "2 ^ _ - 1"]
    by (auto
      intro!: sum.reindex_bij_witness[of _ Utils_Compat_Discrete.floor_log \<open>power 2\<close>]
      simp add: sum_distrib_left)

  text
    \<open>Upper bound by a partial geometric series, taken over all r \<in> nat
    up to `2 ^ l`.\<close>
  also have \<open>\<dots> \<le> 2 * ?exp_term l * (\<Sum> r \<le> 2 ^ l - 1. ?exp_term l ^ r)\<close>
    using diff_le_mono[of "2 ^ _" "2 ^ l" 1]
    by (force intro!: sum_le_included[where i = Suc])

  text \<open>Upper bound by infinite geometric series.\<close>
  also have \<open>\<dots> \<le> 2 * ?exp_term l * (1 / (1 - ?exp_term l))\<close>
    using \<open>?exp_term l < 1\<close> \<open>\<epsilon> > 0\<close>
    by (auto intro: sum_le_suminf simp add: suminf_geometric[symmetric])

  also have \<open>\<dots> \<le> 4 * ?exp_bound\<close>
  proof -
    have
      \<open>2 * x / (1 - x) \<le> 4 * y\<close>
      if \<open>0 \<le> x\<close> \<open>x \<le> y\<close> \<open>y \<le> 1 / 2\<close> for x y :: real
      using that by sos

    then show ?thesis when
      \<open>?exp_term l \<le> ?exp_bound\<close> (is ?thesis_0)
      \<open>?exp_bound \<le> 1 / 2\<close> (is ?thesis_1) 
      using that by simp_all

    from \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close> \<open>\<epsilon> > 0\<close> r_pos 
    show ?thesis_0
      using
        not_less[of "6 * 2 ^ l + \<epsilon> * (2 * 2 ^ l)" "0"]
        of_nat_le_iff[of "threshold * 2 ^ l" "card (set xs) * 2 * r"]
      by (auto
        intro: add_mono
        simp add: field_split_simps power_numeral_reduce pos_add_strict)

    have
      \<open>4 * r * (1 + 1 * \<epsilon> / 3) \<le> \<epsilon>\<^sup>2 * threshold\<close>
      if \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close> \<open>r \<ge> 1\<close> for r threshold :: real
      using \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> that by sos

    with \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close> \<open>\<epsilon> > 0\<close> r_pos
    have \<open>?exp_bound \<le> exp (- 1)\<close> by simp

    with exp_minus_one_le_half show ?thesis_1 by argo
  qed

  finally show ?thesis unfolding prob_k_le_l_and_est_out_of_range_bound_def .
qed

end

end

end