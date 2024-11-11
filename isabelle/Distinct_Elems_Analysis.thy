section \<open> TODO \<close>
theory Distinct_Elems_Analysis

imports
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

    with assm snoc.prems show False by fastforce 
  qed
qed

context
  fixes xs :: \<open>'a list\<close>
begin

abbreviation
  \<open>run_with_bernoulli_matrix f \<equiv>
    map_pmf (f xs) (fair_bernoulli_matrix (length xs) (length xs))\<close>

lemma estimate_distinct_error_bound_fail_2:
  assumes
    (* This says that l \<ge> log2 (3F_0 / threshold) *)
    \<open>2 ^ l * threshold \<ge> 3 * (card <| set xs)\<close>
  shows
    \<open>\<P>(state in
      run_with_bernoulli_matrix (run_reader <<< eager_algorithm).
      state_k state > l)
    \<le> real (length xs) * exp (- real threshold / 6)\<close>
    (is \<open>?L \<le> _ * exp ?exponent\<close>)
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

  also have \<open>\<dots> \<le> (\<Sum> i < length xs. exp ?exponent)\<close>
  proof (rule sum_mono, simp only: lessThan_iff)
    fix i assume \<open>i < length xs\<close>
    show \<open>?prob i \<le> exp ?exponent\<close>
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
      then have \<open>n \<ge> 1\<close> by (simp add: leI n_def)

      moreover have
        \<open>\<alpha> \<ge> 3\<close> and [simp] : \<open>threshold = \<alpha> * \<mu>\<close>
        using
          \<open>n \<ge> 1\<close> \<open>2 ^ l * threshold \<ge> 3 * (card <| set xs)\<close>
          card_set_take_le_card_set[of \<open>Suc i\<close> xs]
          of_nat_le_iff[of "3 * card (set (take (Suc i) xs))" "threshold * 2 ^ l"] 
        by (auto simp add: \<alpha>_def n_def field_simps)

      moreover have
        \<open>- (real n * (\<alpha> - 1)\<^sup>2 / (2 ^ l * (2 + (2 * \<alpha> - 2) / 3)))
        \<le> ?exponent\<close>
        using \<open>n \<ge> 1\<close> \<open>\<alpha> \<ge> 3\<close>
        apply (simp add: field_split_simps power_numeral_reduce add_increasing)
        by (smt (verit, ccfv_threshold) mult_sign_intros(1) two_realpow_ge_one)

      ultimately show ?thesis
        using binomial_distribution.chernoff_prob_ge[
          of p, simplified binomial_distribution_def]
        apply simp
        by (smt (verit, ccfv_SIG) Collect_cong Groups.mult_ac(2) exp_le_cancel_iff n_def) 
    qed
  qed

  finally show ?thesis by simp
qed

lemma estimate_distinct_error_bound_l_binom:
  assumes
    \<open>\<epsilon> > 0\<close>
    \<open>l \<le> length xs\<close>
  defines
    [simp] :
      \<open>exp_term k \<equiv>
        exp (- real (card <| set xs) * \<epsilon>\<^sup>2 / (2 ^ k * (2 + 2 * \<epsilon> / 3)))\<close>
  shows
    \<open>\<P>(state in run_with_bernoulli_matrix <| run_reader <<< eager_algorithm.
      state_k state \<le> l \<and>
      real (compute_estimate state) >[\<epsilon>] card (set xs))
    \<le> (xs |> case_list 0 \<lblot>\<lblot>2 * exp_term l / (1 - exp_term l)\<rblot>\<rblot>)\<close>
    (is \<open>?L (\<le>) l \<le> _\<close>)
proof (cases xs)
  case Nil
  then show ?thesis
    by (simp add: eager_algorithm_def run_steps_from_state_def run_reader_simps initial_state_def compute_estimate_def)
next
  case (Cons _ _)

  then have \<open>exp_term k < 1\<close> for k
    using \<open>\<epsilon> > 0\<close>
    by (simp add: field_split_simps add_strict_increasing2 card_gt_0_iff)

  let ?binom_mean = \<open>\<lambda> k. real (card <| set xs) / 2 ^ k\<close>

  (* Splits the error event for k=0, k=1,...,k=l *)
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

  (* Now we go into nondeterministic *)
  also have \<open>\<dots> \<le> (
    \<Sum> k \<le> l.
      \<P>(estimate in run_with_bernoulli_matrix <| nondet_alg k.
        2 ^ k * real estimate >[\<epsilon>] real (card <| set xs)))\<close>
    by (auto
      intro: sum_mono pmf_mono
      simp add:
        nondet_alg_def compute_estimate_def algebra_simps
        eager_algorithm_inv[unfolded eager_state_inv_def])

  also have \<open>\<dots> \<le> (
    \<Sum> k \<le> l.
      \<P>(estimate in binomial_pmf (card <| set xs) <| 1 / 2 ^ k.
        \<bar>real estimate - ?binom_mean k\<bar> \<ge> \<epsilon> * ?binom_mean k))\<close>
    (is \<open>_ \<le> (\<Sum> k \<le> _. ?L k)\<close>)
    using assms
    by (auto
      intro!: sum_mono intro: pmf_mono
      simp add:
        map_pmf_nondet_alg_eq_binomial[
          where m = \<open>length xs\<close>, where n = \<open>length xs\<close>, symmetric]
        field_simps)

  also have \<open>\<dots> \<le> (\<Sum> k \<le> l. 2 * exp_term k)\<close> (is \<open>_ \<le> (\<Sum> k \<le> _. ?R k)\<close>)
  proof (rule sum_mono)
    fix k
    from
      binomial_distribution.chernoff_prob_abs_ge[
        where n = \<open>card <| set xs\<close>, where p = \<open>1 / 2 ^ k\<close>, where \<delta> = \<epsilon>,
        simplified binomial_distribution_def]
      \<open>\<epsilon> > 0\<close>
    show \<open>?L k \<le> ?R k\<close> by (simp add: field_simps)
  qed

  also have
    \<open>\<dots> = (\<Sum> k \<le> l. 2 * exp_term l ^ 2 ^ (l - k))\<close> (is \<open>_ = sum ?g _\<close>)
    apply (rule sum.cong, blast)
    using \<open>\<epsilon> > 0\<close>
    apply (simp add: exp_of_nat_mult[symmetric] power_add[symmetric] field_split_simps)
    by (smt (verit, best) mult_sign_intros(5) one_le_power)

  also have \<open>\<dots> = 2 * exp_term l * (\<Sum> r \<in> (^) 2 ` {.. l}. exp_term l ^ (r - 1))\<close>
    using
      sum.atLeastAtMost_rev[of ?g 0 l, simplified atLeast0AtMost]
      power_add[of "exp_term l" "1" "2 ^ _ - 1"]
    by (auto
      intro: sum.reindex_bij_witness[of _ Discrete.log \<open>(^) 2\<close>]
      simp add: sum_distrib_left)

  also have \<open>\<dots> \<le> 2 * exp_term l * (\<Sum> r \<le> 2 ^ l - 1. exp_term l ^ r)\<close>
    using
      semiring_norm(92)[of "num.Bit0 num.One"] pos2 zero_less_power[of "2"]
      Suc_pred[of "2 ^ _"] diff_le_mono[of "2 ^ _" "2 ^ l" "Suc 0"]
      power_increasing[of _ l "2"]
    by (force intro: sum_le_included[where i = Suc]) 

  also have \<open>\<dots> \<le> 2 * exp_term l * (1 / (1 - exp_term l))\<close>
    using \<open>exp_term l < 1\<close> \<open>\<epsilon> > 0\<close>
    by (auto intro: sum_le_suminf simp add: suminf_geometric[symmetric])

  finally show ?thesis by (simp add: Cons) 
qed

lemma estimate_distinct_error_bound:
  assumes "(l::nat) = undefined"
  shows "
    \<P>(n in estimate_distinct xs.
      n |> fail_or_satisfies (beyond_eps_range_of_card xs))
     \<le> real (length xs) / 2 ^ threshold + bar \<epsilon> thresh"
  (is "?l \<le> ?R")
proof -
  have *: "estimate_distinct_no_fail xs =
     map_pmf compute_estimate
     (map_pmf
       (run_reader (eager_algorithm xs))
       (fair_bernoulli_matrix (length xs) (length xs)))" (is "_ =  map_pmf compute_estimate ?E")   
    unfolding estimate_distinct_no_fail_eq_lazy_algo
    apply (subst eager_lazy_conversion)
    by auto

  have "?l \<le> real (length xs) / 2 ^ threshold
    + \<P>(n in estimate_distinct_no_fail xs.
       n |> (beyond_eps_range_of_card xs))"
    by (intro prob_estimate_distinct_fail_or_satisfies_le)
  
  moreover have "... =
    real (length xs) / 2 ^ threshold
      + \<P>(st in ?E.
        beyond_eps_range_of_card xs (compute_estimate st))"
    unfolding *
    by auto
  moreover have "... \<le>
    real (length xs) / 2 ^ threshold
      + \<P>(st in ?E. state_k st > l)
      + \<P>(st in ?E. 
        state_k st \<le> l \<and>
          beyond_eps_range_of_card xs (compute_estimate st))"
    by (auto intro!: pmf_add)
 
  ultimately show ?thesis
    sorry
qed

end

end
