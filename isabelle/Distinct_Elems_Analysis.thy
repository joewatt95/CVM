section \<open> TODO \<close>
theory Distinct_Elems_Analysis

imports
  "HOL-Library.Sum_of_Squares"
  CVM.Distinct_Elems_Algo
  CVM.Distinct_Elems_No_Fail
  CVM.Distinct_Elems_Eager
  CVM.Distinct_Elems_Binomial
  CVM.Utils_Real
  CVM.Utils_Concentration_Inequalities
  CVM.Utils_Reader_Monad_Hoare
  CVM.Utils_Reader_Monad_Relational

begin

locale with_threshold_and_eps = with_threshold +
  fixes \<epsilon> :: real
  assumes eps_pos : \<open>\<epsilon> > 0\<close>
begin

definition
  eager_algorithm_then_step_1 ::
  \<open> nat \<Rightarrow> 'a list \<Rightarrow> (nat \<times> nat \<Rightarrow> bool) \<Rightarrow> 'a state\<close> where 
  \<open>eager_algorithm_then_step_1 i xs \<equiv>
    run_reader (eager_algorithm (take i xs) \<bind> eager_step_1 xs i)\<close>

(* lemma contrapos_state_k_lt_l:
  assumes "\<And> i. i < length xs \<Longrightarrow>
  (
    let st = eager_algorithm_then_step_1 i xs \<phi> in
    \<not> (state_k st = l \<and> card (state_chi st) \<ge> threshold)
  )"
  shows "state_k (run_reader (eager_algorithm xs) \<phi>) \<le> l"
  using assms
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case
    by (auto simp add: eager_algorithm_def run_steps_from_state_def eager_step_def run_reader_simps initial_state_def)
next
  case ih:(snoc x xs)
  define stx where "stx \<equiv> run_reader (eager_algorithm xs) \<phi>"
  have *:"i < length xs \<Longrightarrow>
    eager_step_1 (xs @ [x]) i = eager_step_1 xs i" for i
    by (auto intro!: eager_step_cong)
  have 1: "state_k stx \<le> l"
    unfolding stx_def
    apply (intro ih(1))
    subgoal for i
      using ih(2)[of i] unfolding Let_def eager_algorithm_then_step_1_def
      using * by auto
    done

  define sty where "sty \<equiv> run_reader (eager_step_1 (xs @ [x]) (length xs) stx) \<phi>"
  have stky: "state_k sty = state_k stx"
    unfolding sty_def
    by (auto simp add: eager_step_1_def run_reader_simps)

  from ih(2)[of "length xs"]
  have "\<not> (state_k sty = l \<and> card (state_chi sty) \<ge> threshold)"
    by (auto simp add: run_reader_simps stx_def[symmetric] sty_def[symmetric] eager_algorithm_then_step_1_def)
 
  then have "state_k sty < l \<or> state_k sty = l \<and> card (state_chi sty) < threshold"
    by (metis "1" antisym_conv1 not_le_imp_less stky)

  thus ?case
  by (auto simp add: eager_algorithm_snoc run_reader_simps stx_def[symmetric] eager_step_def sty_def[symmetric] eager_step_2_def Let_def)
qed *)

lemma exists_index_threshold_exceeded_of_k_exceeds :
  assumes \<open>state_k (run_reader (eager_algorithm xs) \<phi>) > l\<close>
  shows
    \<open>\<exists> i < length xs.
      state_k (eager_algorithm_then_step_1 i xs \<phi>) = l \<and>
      card (state_chi <| eager_algorithm_then_step_1 i xs \<phi>) \<ge> threshold\<close>
using assms proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by (simp add: eager_algo_simps eager_algorithm_def)
next
  let ?P = \<open>\<lambda> xs length.
    \<forall> i.
      state_k (eager_algorithm_then_step_1 i xs \<phi>) = l \<longrightarrow>
      i < length \<longrightarrow>
      card (state_chi <| eager_algorithm_then_step_1 i xs \<phi>) < threshold\<close>

  case (snoc x xs)
  then have ih :
    \<open>?P xs (length xs) \<Longrightarrow> state_k (run_reader (eager_algorithm xs) \<phi>) \<le> l\<close>
    using not_le by blast

  show ?case
  proof (rule ccontr, simp add: not_le)
    note [simp] = eager_algo_simps eager_algorithm_then_step_1_def
    note [split] = if_splits

    assume assm : \<open>?P (xs @ [x]) <| Suc <| length xs\<close>

    then have
      \<open>card (state_chi <| eager_algorithm_then_step_1 i xs \<phi>) < threshold\<close>
      if
        \<open>i < length xs\<close>
        \<open>state_k (eager_algorithm_then_step_1 i xs \<phi>) = l\<close>
      for i
      using that
      apply simp
      by (metis less_Suc_eq nth_append)

    with ih have \<open>state_k (run_reader (eager_algorithm xs) \<phi>) \<le> l\<close> by blast

    with assm snoc.prems show False by auto
  qed
qed

context
  fixes
    l :: nat and
    xs :: \<open>'a list\<close>
begin

abbreviation
  \<open>run_with_bernoulli_matrix f \<equiv>
    map_pmf (f xs) (fair_bernoulli_matrix (length xs) (length xs))\<close>

lemma prob_eager_algo_k_gt_l_le :
  assumes
    \<open>2 ^ l * threshold \<ge> r * card (set xs)\<close>
    \<open>r \<ge> 2\<close>
  shows
    \<open>\<P>(state in
      run_with_bernoulli_matrix <| run_reader <<< eager_algorithm.
      state_k state > l)
    \<le> real (length xs) * exp (- real threshold / 6)\<close>
    (is \<open>?L \<le> _ * ?exp_term\<close>)
proof (cases \<open>l > length xs\<close>)
  case True
  with eager_algorithm_k_bounded
  have \<open>?L = 0\<close>
    apply (simp add: measure_pmf.prob_eq_0 AE_measure_pmf_iff)
    using order_trans_rules(20,21) by blast
  then show ?thesis by simp
next
  case False
  then have \<open>l \<le> length xs\<close> by simp

  (* We exceed l iff we hit a state where k = l, |X| \<ge> threshold
    after running eager_step_1.
    TODO: can this me made cleaner with only eager_algorithm? *)
  have \<open>?L \<le>
    \<P>(\<phi> in fair_bernoulli_matrix (length xs) (length xs).
      \<exists> i < length xs. (
        let state = eager_algorithm_then_step_1 i xs \<phi>
        in state_k state = l \<and> card (state_chi state) \<ge> threshold))\<close>
    using exists_index_threshold_exceeded_of_k_exceeds[of l xs]
    by (auto intro: pmf_mono simp add: Let_def)

  (* union bound *)
  also have \<open>\<dots> \<le> (
    \<Sum> i < length xs.
      \<P>(\<phi> in fair_bernoulli_matrix (length xs) (length xs).
        let st = eager_algorithm_then_step_1 i xs \<phi>
        in state_k st = l \<and> card (state_chi st) \<ge> threshold))\<close>
    proof -
      have [simp] : \<open>{\<omega>. \<exists> i < n. P i \<omega>} = (\<Union> i < n. {\<omega>. P i \<omega>})\<close>
        for n and P :: \<open>nat \<Rightarrow> 'b \<Rightarrow> bool\<close> by blast
      show ?thesis by (auto intro: measure_pmf.finite_measure_subadditive_finite)
    qed

  also have \<open>\<dots> \<le> (
    \<Sum> i < length xs.
      \<P>(estimate in run_with_bernoulli_matrix <| nondet_alg l <<< take (Suc i).
        real estimate \<ge> threshold))\<close>
    apply (rule sum_mono)
    apply (simp add: eager_algorithm_then_step_1_def nondet_alg_def Let_def)
    by (smt (verit, best) eager_algorithm_inv eager_state_inv_def eager_step_1_inv mem_Collect_eq pmf_mono run_reader_simps(3) semiring_norm(174))

  also have \<open>\<dots> = (
    \<Sum> i < length xs.
      \<P>(estimate in binomial_pmf (card <| set <| take (Suc i) xs) (1 / 2 ^ l).
        real estimate \<ge> threshold))\<close>
    (is \<open>_ = sum ?prob _\<close>)
    by (auto
      intro: sum.cong
      simp add:
        map_pmf_nondet_alg_eq_binomial[
          where m = \<open>length xs\<close>, where n = \<open>length xs\<close>, symmetric]
        \<open>l \<le> length xs\<close>)

  also have \<open>\<dots> \<le> real (length xs) * ?exp_term\<close>
  proof (rule sum_bounded_above[where A = \<open>{..< length xs}\<close>, simplified card_lessThan])
    fix i show \<open>?prob i \<le> ?exp_term\<close>
    proof (cases xs)
      case Nil
      then show ?thesis
        by (simp add: binomial_pmf_0 threshold_pos eager_algorithm_def run_steps_from_state_def run_reader_simps initial_state_def)
    next
      define p :: real and n \<mu> \<alpha> where
        [simp] : \<open>p \<equiv> 1 / 2 ^ l\<close> and
        \<open>n \<equiv> card (set <| take (Suc i) xs)\<close> and
        [simp] : \<open>\<mu> \<equiv> n * p\<close> and
        \<open>\<alpha> \<equiv> threshold / \<mu>\<close>

      case (Cons _ _)
      then have \<open>n \<ge> 1\<close> by (simp add: n_def leI)
      then have \<open>\<alpha> \<ge> r\<close> and [simp] : \<open>threshold = \<alpha> * \<mu>\<close>
        using
          \<open>2 ^ l * threshold \<ge> r * (card <| set xs)\<close>
          card_set_take_le_card_set[of "Suc i" xs]
          of_nat_le_iff[of "r * card (set (take (Suc i) xs))" "threshold * 2 ^ l"] 
          mult_le_mono2[of "card (set (take (Suc i) xs))" "card (set xs)" r] order.trans[of "r * card (set (take (Suc i) xs))" "r * card (set xs)" "threshold * 2 ^ l"]
        by (auto simp add: \<alpha>_def n_def field_simps)

      with binomial_distribution.chernoff_prob_ge[
        of p \<open>\<alpha> - 1\<close> n, simplified binomial_distribution_def]
      have \<open>?prob i \<le> exp (- real n * p * (\<alpha> - 1)\<^sup>2 / (2 + 2 * (\<alpha> - 1) / 3))\<close>
        using \<open>r \<ge> 2\<close> by (simp add: n_def algebra_simps)

      also have \<open>\<dots> \<le> ?exp_term\<close>
      proof -
        have
          \<open>c * (16 * \<alpha>\<^sup>2 - 40 * \<alpha> + 18) \<ge> 0\<close> if \<open>c \<ge> 0\<close> \<open>\<alpha> \<ge> 2\<close> for c \<alpha> :: real
          using that by sos

        from this[of \<open>real n * 2 ^ l\<close> \<alpha>]
        show ?thesis
          using \<open>n \<ge> 1\<close> \<open>\<alpha> \<ge> r\<close> \<open>r \<ge> 2\<close> order.trans[of "4 * 2 ^ l" "4 * 2 ^ l + \<alpha> * (2 * 2 ^ l)" "0"] 
          by (simp add:
            field_split_simps power_numeral_reduce add_increasing less_le_not_le)
      qed

      finally show ?thesis .
    qed
  qed

  finally show ?thesis .
qed

context
  fixes r
  assumes
    \<open>threshold \<ge> r\<close>
    \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close>
begin

lemma l_le_length_xs :
  \<open>l \<le> length xs\<close>
proof -
  from \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close>
  have \<open>l \<le> Discrete.log (2 * r * card (set xs) div threshold)\<close>
    by (metis Discrete.log_le_iff less_eq_div_iff_mult_less_eq log_power threshold_pos)

  also have \<open>\<dots> \<le> Discrete.log (2 * length xs)\<close>
    apply (rule Discrete.log_le_iff)
    using \<open>threshold \<ge> r\<close>
    by (smt (verit, best) card_length div_le_mono le_trans less_eq_nat.simps(1) mult.commute mult.left_commute mult_le_mono1 nonzero_mult_div_cancel_right
      semidom_div_by_0)

  also have \<open>\<dots> \<le> length xs\<close>
    by (metis Discrete.log_le_iff less_exp log_exp2_le log_power log_twice nat_0_less_mult_iff not_le not_less_eq_eq order_class.order_eq_iff self_le_ge2_pow zero_le)

  finally show ?thesis .
qed

lemma prob_eager_algo_k_le_l_and_estimate_out_of_range_le :
  assumes \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close>
  shows
    \<open>\<P>(state in run_with_bernoulli_matrix <| run_reader <<< eager_algorithm.
      state_k state \<le> l \<and>
      real (compute_estimate state) >[\<epsilon>] card (set xs))
    \<le> 4 * exp (- \<epsilon>\<^sup>2 * threshold / (2 * real r * (2 + 2 * \<epsilon> / 3)))\<close>
    (is \<open>?L (\<le>) l \<le> 4 * ?exp_bound\<close>)
proof (cases xs)
  case Nil
  then show ?thesis
    using \<open>\<epsilon> > 0\<close>
    by (simp add: eager_algo_simps eager_algorithm_def compute_estimate_def)
next
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
      intro!: sum.reindex_bij_witness[of _ Discrete.log \<open>power 2\<close>]
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
      using that by auto

    from threshold_pos \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close>
    have \<open>r > 0\<close> using gr0I[of r] by fastforce

    with \<open>\<epsilon> > 0\<close> \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close>
    show ?thesis_0
      using
        not_less[of "6 * 2 ^ l + \<epsilon> * (2 * 2 ^ l)" "0"]
        of_nat_le_iff[of "threshold * 2 ^ l" "card (set xs) * 2 * r"]
      by (auto
        intro: add_mono
        simp add: field_split_simps power_numeral_reduce pos_add_strict)

    have
      \<open>2 * r * (2 + 2 * \<epsilon> / 3) \<le> \<epsilon>\<^sup>2 * threshold\<close>
      if \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close> \<open>r \<ge> 1\<close> for r threshold :: real
      using \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> that by sos

    with \<open>\<epsilon> > 0\<close> \<open>r > 0\<close> \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close>
    have \<open>?exp_bound \<le> exp (- 1)\<close> by simp

    with exp_minus_one_le_half show ?thesis_1 by argo
  qed

  finally show ?thesis .
qed

(* theorem estimate_distinct_error_bound:
  defines
    [simp] : \<open>prob_fail_bound \<equiv> real (length xs) / 2 ^ threshold\<close> and
    [simp] : \<open>prob_eager_algo_k_gt_l_le_bound \<equiv>
      real (length xs) * exp (- real threshold / 6)\<close> and
    [simp] : \<open>prob_eager_algo_k_le_l_and_estimate_out_of_range_bound \<equiv>
      2 / (exp (\<epsilon>\<^sup>2 * real threshold / (16 + 16 * \<epsilon> / 3)) - 1)\<close>
  shows
    \<open>\<P>(estimate in estimate_distinct xs.
        estimate |> fail_or_satisfies
          (\<lambda> estimate. real estimate >[\<epsilon>] card (set xs)))
    \<le> prob_fail_bound +
      prob_eager_algo_k_gt_l_le_bound +
      prob_eager_algo_k_le_l_and_estimate_out_of_range_bound\<close>
    (is \<open>?L \<le> _\<close>)
proof (cases xs)
  case Nil
  then show ?thesis
    using threshold_pos \<open>\<epsilon> > 0\<close>
    by (simp add:
      estimate_distinct_def run_steps_then_estimate_def compute_estimate_def
      initial_state_def)
next
  case (Cons _ _)

  let ?run_eager_algo =
    \<open>run_with_bernoulli_matrix <| run_reader <<< eager_algorithm\<close>

  have \<open>?L \<le>
    prob_fail_bound +
    \<P>(estimate in estimate_distinct_no_fail xs.
      real estimate >[\<epsilon>] card (set xs))\<close>
    using prob_estimate_distinct_fail_or_satisfies_le by auto

  also have \<open>\<dots> \<le>
      prob_fail_bound +
      \<P>(state in ?run_eager_algo. state_k state > l) +
      \<P>(state in ?run_eager_algo. 
        state_k state \<le> l \<and> real (compute_estimate state) >[\<epsilon>] card (set xs))\<close>
    by (auto
      intro: prob_estimate_distinct_fail_or_satisfies_le pmf_add
      simp add:
        estimate_distinct_no_fail_eq_lazy_algo
        eager_lazy_conversion[of _ \<open>length xs\<close>])

  finally show ?thesis
    using
      prob_eager_algo_k_gt_l_le
      prob_eager_algo_k_le_l_and_estimate_out_of_range_le
    apply simp
    sorry
qed *)

end

end

end