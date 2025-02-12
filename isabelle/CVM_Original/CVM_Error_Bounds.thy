theory CVM_Error_Bounds

imports
  "HOL-Decision_Procs.Approximation"
  CVM_Algo_Nondet_Binomial
  Utils_Concentration_Inequalities

begin

locale cvm_error_bounds = cvm_algo + fixes
  r l :: nat and
  \<epsilon> :: real and
  xs :: \<open>'a list\<close>
begin

abbreviation
  \<open>run_with_bernoulli_matrix \<equiv> \<lambda> g.
    map_pmf (g xs) (bernoulli_matrix (length xs) (length xs) f)\<close>

text \<open>Bound for the case when k <= l\<close>
definition
  \<open>prob_k_le_l_and_est_out_of_range_bound \<equiv>
    4 * exp (-\<epsilon>\<^sup>2 * threshold / (4 * real r * (1 + \<epsilon> / 3)))\<close>

text \<open>Bound for the case when k > l\<close>
definition
  \<open>prob_k_gt_l_bound \<equiv>
    real (length xs) *
    exp (-3 * real threshold * (r - 1)\<^sup>2 / (5 * r + 2 * r\<^sup>2))\<close>

end

locale cvm_error_bounds_assms = cvm_error_bounds + cvm_algo_assms
begin

subsection \<open>Proof for k <= l case.\<close>

context
  assumes
    \<open>threshold \<ge> r\<close>
    \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close>
begin

lemma l_le_length_xs :
  \<open>l \<le> length xs\<close>
proof -
  from \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close>
  have \<open>l \<le> floor_log (2 * r * card (set xs) div threshold)\<close>
    by (metis floor_log_le_iff less_eq_div_iff_mult_less_eq floor_log_power threshold)

  also from \<open>threshold \<ge> r\<close> threshold
  have \<open>\<dots> \<le> floor_log (2 * length xs)\<close>
    by (smt (verit, del_insts) Groups.mult_ac(2,3) card_length div_mult_self1_is_m floor_log_le_iff less_eq_div_iff_mult_less_eq mult_le_mono nat_le_linear
      verit_la_disequality)

  also have \<open>\<dots> \<le> length xs\<close>
    by (metis floor_log_le_iff less_exp floor_log_exp2_le floor_log_power floor_log_twice nat_0_less_mult_iff not_le not_less_eq_eq order_class.order_eq_iff self_le_ge2_pow zero_le)

  finally show ?thesis .
qed

lemma r_pos :
  \<open>r > 0\<close>
  using \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close> threshold power_eq_0_iff
  by fastforce

theorem prob_eager_algo_k_le_l_and_est_out_of_range_le :
  assumes \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close>
  shows
    \<open>\<P>(state in run_with_bernoulli_matrix <|
        run_reader <<< flip run_steps_eager initial_state.
      state_k state \<le> l \<and> compute_estimate state >[\<epsilon>] card (set xs))
    \<le> prob_k_le_l_and_est_out_of_range_bound\<close>
    (is \<open>?L (\<le>) l \<le> _\<close>)
proof (cases xs)
  case Nil
  with \<open>\<epsilon> > 0\<close> show ?thesis
    unfolding
      compute_estimate_def prob_k_le_l_and_est_out_of_range_bound_def
      initial_state_def
    by (simp add: run_reader_simps)
next
  case (Cons _ _)

  let ?exp_bound =
    \<open>exp (-\<epsilon>\<^sup>2 * threshold / (4 * real r * (1 + \<epsilon> / 3)))\<close>
  let ?exp_term = \<open>\<lambda> k.
    exp (- (real (card (set xs)) * f ^ k * \<epsilon>\<^sup>2 / (2 + 2 * \<epsilon> / 3)))\<close>
  let ?binom_mean = \<open>\<lambda> k. f ^ k * real (card <| set xs)\<close>

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

  text \<open>Transform to binomial distribution and weaken > to >=.\<close>
  also have \<open>\<dots> \<le> (
    \<Sum> k \<le> l.
      \<P>(estimate in binomial_pmf (card <| set xs) <| f ^ k.
        \<bar>real estimate - ?binom_mean k\<bar> \<ge> \<epsilon> * ?binom_mean k))\<close>
    (is \<open>(\<Sum> k \<le> _. ?L k) \<le> (\<Sum> k \<le> _. ?R k)\<close>)
  proof (intro sum_mono, unfold atMost_iff)
    fix k assume \<open>k \<le> l\<close>
    with
      \<open>\<epsilon> > 0\<close> l_le_length_xs
      prob_eager_algo_le_binomial[where
        k = k and xs = xs and m = \<open>length xs\<close> and n = \<open>length xs\<close> and
        P = \<open>\<lambda> est. est / f ^ k >[\<epsilon>] card (set xs)\<close>]
    show \<open>?L k \<le> ?R k\<close>
      unfolding compute_estimate_def
      apply (simp add: Let_def field_simps)
      by (smt (verit, ccfv_threshold) mem_Collect_eq mult.commute pmf_mono)
  qed

  text \<open>Apply Chernoff bound to each term.\<close>
  also have
    \<open>\<dots> \<le> (\<Sum> k \<le> l. 2 * ?exp_term k)\<close> (is \<open>(\<Sum> k \<le> _. ?L k) \<le> (\<Sum> k \<le> _. ?R k)\<close>)
  proof (intro sum_mono)
    fix k
    from \<open>\<epsilon> > 0\<close>
      binomial_distribution.chernoff_prob_abs_ge[
        where n = \<open>card <| set xs\<close> and p = \<open>f ^ k\<close> and \<delta> = \<epsilon>]
    show \<open>?L k \<le> ?R k\<close>
      unfolding binomial_distribution_def
      by (simp add: power_le_one algebra_simps)
  qed

  text
    \<open>In preparation to bound via a geometric series, we first transform each
    term to be of the form `2 * exp_term l * 2 ^ r` so that we can later pull
    out a factor of `2 * exp_term l` from each term.
    Note that `exp_term l < 1` and that this is important for obtaining a tight
    bound later on.\<close>
  also from \<open>\<epsilon> > 0\<close> have
    \<open>\<dots> = (\<Sum> k \<le> l. 2 * ((?exp_term l) powr (1 / f ^ (l - k))))\<close>
    (is \<open>_ = (\<Sum> k \<le> _. ?g k)\<close>)
    apply (intro sum.cong refl)
    apply (simp add: exp_powr_real field_split_simps)
    unfolding Multiseries_Expansion.intyness_simps
    by (smt (verit, best) Multiseries_Expansion.intyness_simps(5) linordered_semidom_class.add_diff_inverse more_arith_simps(11) mult.commute mult_pos_pos not_less of_nat_0_less_iff power_add
      rel_simps(51) zero_less_power)

  text
    \<open>Now we do the following:
    1. Reverse the summation from `l --> 0`, to `0 --> l`
    2. Reindex the sum to be taken over exponents `r` of the form `2 ^ k`
       instead of being over all `k`.
    3. Pull out a factor of `2 * exp_term l` from each term.\<close>
  also have
    \<open>\<dots> = 2 * ?exp_term l * (\<Sum> r \<in> power 2 ` {.. l}. ?exp_term l ^ (r - 1))\<close>
    unfolding
      sum_distrib_left
      sum.atLeastAtMost_rev[of ?g 0 l, simplified atLeast0AtMost]
    apply (intro sum.reindex_bij_witness[of _ floor_log \<open>power 2\<close>])
    by (auto
      simp flip: exp_of_nat_mult exp_add
      simp add: exp_powr_real field_split_simps)

  text
    \<open>Upper bound by a partial geometric series, taken over all r \<in> nat
    up to `2 ^ l`.\<close>
  also have \<open>\<dots> \<le> 2 * ?exp_term l * (\<Sum> r \<le> 2 ^ l - 1. ?exp_term l ^ r)\<close>
    apply (intro mult_mono sum_le_included[where i = Suc] sum_nonneg)
    apply simp_all
    by (meson Suc_pred atMost_iff diff_le_mono less_eq_real_def nat_zero_less_power_iff pos2 power_increasing rel_simps(25))

  text \<open>Upper bound by infinite geometric series.\<close>
  also have \<open>\<dots> \<le> 2 * ?exp_term l * (1 / (1 - ?exp_term l))\<close>
  proof -
    from Cons \<open>\<epsilon> > 0\<close> have \<open>?exp_term l < 1\<close> using order_less_le by fastforce
    with \<open>\<epsilon> > 0\<close> show ?thesis
      by (auto intro: sum_le_suminf simp flip: suminf_geometric)
  qed

  also have \<open>\<dots> \<le> 4 * ?exp_bound\<close>
  proof -
    have
      \<open>2 * x / (1 - x) \<le> 4 * y\<close>
      if \<open>0 \<le> x\<close> \<open>x \<le> y\<close> \<open>y \<le> 1 / 2\<close> for x y :: real
      using that
      by (sos "((((A<0 * A<1) * R<1) + (((A<=1 * (A<0 * R<1)) * (R<4 * [1]^2)) + ((A<=0 * (A<=2 * (A<0 * R<1))) * (R<2 * [1]^2)))))")

    then show ?thesis when
      \<open>?exp_term l \<le> ?exp_bound\<close> (is ?thesis_0)
      \<open>?exp_bound \<le> 1 / 2\<close> (is ?thesis_1) 
      using that by simp_all

    from \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close> \<open>\<epsilon> > 0\<close> r_pos threshold
    show ?thesis_0
      by (auto
        intro!: add_mono
        simp add: field_split_simps pos_add_strict approximation_preproc_nat(13))

    from \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> have
      \<open>4 * r * (1 + 1 * \<epsilon> / 3) \<le> \<epsilon>\<^sup>2 * threshold\<close>
      if \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close> \<open>r \<ge> 1\<close> for r threshold
      using that
      by (sos "((R<1 + (((A<1 * R<1) * (R<3/2 * [1]^2)) + (((A<=2 * R<1) * (R<1 * [1]^2)) + (((A<=1 * R<1) * (R<3/2 * [1]^2)) + (((A<=0 * R<1) * (R<2 * [1]^2)) + ((A<=0 * (A<=2 * R<1)) * (R<2 * [1]^2))))))))")

    with \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close> \<open>\<epsilon> > 0\<close> r_pos
    have \<open>?exp_bound \<le> exp (- 1)\<close> by simp
    also have \<open>\<dots> \<le> 1 / 2\<close> by (approximation 0)
    finally show ?thesis_1 .
  qed

  finally show ?thesis unfolding prob_k_le_l_and_est_out_of_range_bound_def .
qed

subsection \<open>Proof for k > l case.\<close>

abbreviation
  \<open>run_steps_eager_then_step_1 \<equiv> \<lambda> i xs.
    run_steps_eager (take i xs) initial_state \<bind> step_1_eager xs i\<close>

lemma exists_index_threshold_exceeded_of_k_exceeds :
  assumes \<open>state_k (run_reader (run_steps_eager xs initial_state) \<phi>) > l\<close>
  shows
    \<open>\<exists> i < length xs.
      state_k (run_reader (run_steps_eager_then_step_1 i xs) \<phi>) = l \<and>
      card (state_chi <| run_reader (run_steps_eager_then_step_1 i xs) \<phi>)
      \<ge> threshold\<close>
    (is \<open>?thesis' xs\<close>)
using assms proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by (simp add: run_reader_simps initial_state_def)
next
  case (snoc x xs)
  let ?xs' = \<open>xs @ [x]\<close>
  show ?case
  proof (rule ccontr)
    assume \<open>\<not> ?thesis' ?xs'\<close>
    then have not_thesis' :
      \<open>\<forall> i < length ?xs'.
        state_k (run_reader (run_steps_eager_then_step_1 i ?xs') \<phi>) = l \<longrightarrow>
        card (state_chi <| run_reader (run_steps_eager_then_step_1 i ?xs') \<phi>)
        < threshold\<close>
      (is \<open>?not_thesis' (_ @ _)\<close>) by (simp add: not_le)

    then have \<open>?not_thesis' xs\<close>
      unfolding step_1_eager_def' initial_state_def
      apply (simp add: run_reader_simps split: if_splits)
      by (metis less_Suc_eq nth_append_left)

    with snoc.IH have
      \<open>state_k (run_reader (run_steps_eager xs initial_state) \<phi>) \<le> l\<close>
      (is \<open>?P xs (\<le>)\<close>) using not_le by blast

    then show False
    proof (unfold le_less, elim disjE)
      assume \<open>?P xs (<)\<close>

      then have \<open>?P (xs @ [x]) (\<le>)\<close>
        unfolding run_steps_eager_snoc
        unfolding step_eager_def step_1_eager_def' step_2_eager_def'
        by (simp add: run_reader_simps)

      with snoc.prems show False by simp
    next
      assume \<open>?P xs (=)\<close>

      with snoc.prems have
        \<open>card (state_chi <|
          run_reader (run_steps_eager_then_step_1 (length xs) ?xs') \<phi>)
        = threshold\<close> (is \<open>?Q (=)\<close>)
        unfolding take_length_eq_self run_steps_eager_snoc
        unfolding step_eager_def step_1_eager_def' step_2_eager_def'
        by (auto simp add: run_reader_simps split: if_splits)

      moreover from \<open>?P xs (=)\<close> not_thesis' have \<open>?Q (<)\<close>
        unfolding run_steps_eager_snoc
        unfolding step_1_eager_def'
        apply (simp add: run_reader_simps split: if_splits)
        by (metis append.right_neutral lessI nth_append_length take_length_eq_self)

      ultimately show False by simp
    qed
  qed
qed

end

end