theory Distinct_Elems_Error_Bounds_K_Exceeds_L

imports
  "HOL-Library.Sum_of_Squares"
  CVM.Distinct_Elems_Error_Bounds_Common
  CVM.Distinct_Elems_Algo_Transforms_No_Fail
  CVM.Distinct_Elems_Algo_Transforms_Eager
  CVM.Distinct_Elems_Algo_Transforms_Binomial
  CVM.Utils_Real
  CVM.Utils_Concentration_Inequalities

begin

context with_threshold_pos
begin

definition
  eager_algorithm_then_step_1 ::
  \<open>nat \<Rightarrow> 'a list \<Rightarrow> (nat \<times> nat \<Rightarrow> bool) \<Rightarrow> 'a state\<close> where 
  \<open>eager_algorithm_then_step_1 i xs \<equiv>
    run_reader (eager_algorithm (take i xs) \<bind> eager_step_1 xs i)\<close>

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

end

definition (in with_threshold_r_l_\<epsilon>_xs)
  \<open>prob_k_gt_l_bound \<equiv>
    real (length xs) *
    exp (-3 * real threshold * (r - 1)\<^sup>2 / (5 * r + 2 * r\<^sup>2))\<close>

context with_threshold_pos_r_l_\<epsilon>_xs
begin

theorem prob_eager_algo_k_gt_l_le :
  assumes \<open>r \<ge> 2\<close> \<open>2 ^ l * threshold \<ge> r * card (set xs)\<close>
  shows
    \<open>\<P>(state in
      run_with_bernoulli_matrix <| run_reader <<< eager_algorithm.
      state_k state > l)
    \<le> prob_k_gt_l_bound\<close>
    (is \<open>?L \<le> _\<close>)
proof (cases \<open>l > length xs\<close>)
  case True
  with eager_algorithm_k_bounded
  have \<open>?L = 0\<close>
    using dual_order.strict_trans1
    by (fastforce simp add: measure_pmf.prob_eq_0 AE_measure_pmf_iff)
  then show ?thesis by (simp add: prob_k_gt_l_bound_def) 
next
  case False
  then have \<open>l \<le> length xs\<close> by simp

  let ?exp_term = \<open>exp (-3 * real threshold * (r - 1)\<^sup>2 / (5 * r + 2 * r\<^sup>2))\<close>

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
          where m = \<open>length xs\<close> and n = \<open>length xs\<close>, symmetric]
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
          mult_le_mono2[of "card (set (take (Suc i) xs))" "card (set xs)" r]
          order.trans[of "r * card (set (take (Suc i) xs))" "r * card (set xs)" "threshold * 2 ^ l"]
        by (auto simp add: \<alpha>_def n_def field_simps)

      with binomial_distribution.chernoff_prob_ge[
        of p \<open>\<alpha> - 1\<close> n, simplified binomial_distribution_def]
      have \<open>?prob i \<le> exp (- real n * p * (\<alpha> - 1)\<^sup>2 / (2 + 2 * (\<alpha> - 1) / 3))\<close>
        using \<open>r \<ge> 2\<close> by (simp add: n_def algebra_simps)

      also have \<open>\<dots> \<le> ?exp_term\<close>
      proof -
        have
          \<open>c * (27*\<alpha>\<^sup>2*r - 24*\<alpha>*r\<^sup>2 - 6*\<alpha>*r - 6*\<alpha>\<^sup>2 + 6*r\<^sup>2 - 12*\<alpha> + 15*r) \<ge> 0\<close>
          if \<open>c \<ge> 0\<close> \<open>\<alpha> \<ge> r\<close> \<open>r \<ge> 2\<close> for c r :: real
          apply (rule mult_nonneg_nonneg[OF \<open>c \<ge> 0\<close>])
          using that by sos

        note this[of \<open>2 ^ l * real n\<close> r]

        moreover have \<open>4 * 2 ^ l + \<alpha> * (2 * 2 ^ l) > 0\<close>
          using \<open>\<alpha> \<ge> r\<close> \<open>r \<ge> 2\<close> by (simp add: pos_add_strict)

        ultimately show ?thesis
          using \<open>n \<ge> 1\<close> \<open>\<alpha> \<ge> r\<close> \<open>r \<ge> 2\<close>
          by (auto simp add:
            field_split_simps power_numeral_reduce add_increasing less_le_not_le
            Multiseries_Expansion.of_nat_diff_real)
      qed

      finally show ?thesis .
    qed
  qed

  finally show ?thesis unfolding prob_k_gt_l_bound_def .
qed

end

end