section \<open> TODO \<close>
theory Distinct_Elems_Analysis

imports
  CVM.Distinct_Elems_Algo
  CVM.Distinct_Elems_No_Fail
  CVM.Distinct_Elems_Eager
  CVM.Distinct_Elems_Nondet
  CVM.Utils_Reader_Monad_Hoare
  CVM.Utils_Reader_Monad_Relational
begin

locale with_threshold_and_eps = with_threshold +
  fixes \<epsilon> :: real
  assumes eps_pos : \<open>\<epsilon> > 0\<close>
begin

abbreviation beyond_eps_range_of_card :: \<open>'a list \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>beyond_eps_range_of_card xs n \<equiv> real n >[\<epsilon>] card (set xs)\<close>

lemma
  assumes "finite X"
  shows
    "measure_pmf.prob
    (binomial_pmf (card X) (1 / 2 ^ (K::nat)))
    {t. t \<ge> n} \<le> foo"
  sorry

lemma
  assumes "finite X"
  assumes "\<epsilon> > 0"
  shows
    "measure_pmf.prob
    (binomial_pmf (card X) (1 / 2 ^ (K::nat)))
    {t. beyond_eps_range_of_card xs t} \<le> bar"
  sorry

thm binomial_distribution.prob_ge
thm binomial_distribution.prob_abs_ge

(* Ideas on part of the proof for the big K (ie > L) part. *)

abbreviation
  \<open>finite_state_chi _ state \<equiv> finite (state_chi state)\<close>

abbreviation
  \<open>same_states \<phi> state \<phi>' state' \<equiv>
    finite_state_chi \<phi> state \<and> \<phi> = \<phi>' \<and> state = state'\<close>

lemma initial_state_well_formed :
  \<open>finite_state_chi \<phi> initial_state\<close>
  by (simp add: initial_state_def) 

lemma eager_step_preserves_finiteness :
  fixes xs i
  defines [simp] : \<open>P f \<equiv> \<turnstile>rd \<lbrakk>finite_state_chi\<rbrakk> f xs i \<lbrakk>finite_state_chi\<rbrakk> \<close>
  shows \<open>P eager_step_1\<close> \<open>P eager_step_2\<close> \<open>P eager_step\<close>
proof -
  show \<open>P eager_step_1\<close> \<open>P eager_step_2\<close>
    unfolding eager_step_1_def eager_step_2_def
    by (auto
      intro!:
        Utils_Reader_Monad_Hoare.seq' Utils_Reader_Monad_Hoare.if_then_else Utils_Reader_Monad_Hoare.postcond_true
      simp add: Set.remove_def Let_def map_rd_def)

  then show \<open>P eager_step\<close>
    unfolding eager_step_def by (auto intro: Utils_Reader_Monad_Hoare.seq)
qed

context
  fixes xs :: \<open>'a list\<close>
begin

definition \<open>ith_state i \<equiv> foldM_rd (eager_step (take i xs)) [0 ..< i]\<close>

definition
  \<open>ith_state_then_step_1 i \<equiv> ith_state i >=> eager_step_1 (take (Suc i) xs) i\<close>

lemma ith_state_zero_eq :
  \<open>ith_state 0 = return_rd\<close>
  by (auto simp add: ith_state_def)

context
  fixes
    i :: nat
  assumes i_lt_length_xs : \<open>i < length xs\<close>
begin

lemma ith_state_Suc_eq :
  \<open>ith_state (Suc i) = (ith_state i >=> eager_step (take (Suc i) xs) i)\<close>
  using i_lt_length_xs
  by (fastforce
    intro: arg_cong2[where f = bind_rd] foldM_cong eager_step_cong
    simp add: ith_state_def foldM_rd_snoc take_Suc_conv_app_nth)

lemma ith_state_preserves_same_states :
  defines
    [simp] : \<open>P f \<equiv> \<turnstile>rd \<lbrakk>same_states\<rbrakk> \<langle>f i | f i\<rangle> \<lbrakk>same_states\<rbrakk>\<close> and
    [simp] : \<open>eager_step' g j \<equiv> g (take (Suc j) xs) j\<close>
  shows
    \<open>P (eager_step' eager_step_1)\<close>
    \<open>P (eager_step' eager_step_2)\<close>
    \<open>P (eager_step' eager_step)\<close>
    \<open>P ith_state\<close>
proof -
  show
    \<open>P (eager_step' eager_step_1)\<close>
    \<open>P (eager_step' eager_step_2)\<close>
    by (simp, smt (verit, best) Utils_Reader_Monad_Hoare.hoare_tripleE Utils_Reader_Monad_Relational.relational_hoare_triple_def eager_step_preserves_finiteness rel_rd_def)+

  then show \<open>P (eager_step' eager_step)\<close>
    unfolding eager_step_def by (auto intro: seq')

  then show \<open>P ith_state\<close>
    by (simp, smt (verit, ccfv_threshold) ith_state_def loop_unindexed Utils_Reader_Monad_Hoare.hoare_triple_def Utils_Reader_Monad_Relational.relational_hoare_triple_def eager_step_preserves_finiteness(3) rel_rd_def)
qed

lemma ith_state_k_increases_by_at_most_one : 
  \<open>\<turnstile>rd
    \<lbrakk>same_states\<rbrakk>
    \<langle>ith_state i | ith_state (Suc i)\<rangle>
    \<lbrakk>(\<lambda> \<phi> state \<phi>' state'. state_k state' \<le> Suc (state_k state))\<rbrakk>\<close>
  (is \<open>\<turnstile>rd \<lbrakk>_\<rbrakk> \<langle>_ | _\<rangle> \<lbrakk>?S\<rbrakk>\<close>)
proof -
  note ith_state_preserves_same_states

  moreover have
    \<open>\<turnstile>rd
      \<lbrakk>same_states \<phi> state\<rbrakk>
      eager_step_1 xs i
      \<lbrakk>(\<lambda> _ state'. state_k state = state_k state')\<rbrakk>\<close>
    \<open>\<turnstile>rd
      \<lbrakk>(\<lambda> _ state'. state_k state = state_k state')\<rbrakk>
      eager_step_2 xs i
      \<lbrakk>?S \<phi> state\<rbrakk>\<close>
    for \<phi> state i and xs :: \<open>'a list\<close>
    unfolding eager_step_1_def eager_step_2_def Let_def map_rd_def
    by (auto intro!: Utils_Reader_Monad_Hoare.seq' Utils_Reader_Monad_Hoare.if_then_else Utils_Reader_Monad_Hoare.postcond_true)

  ultimately show ?thesis
    by (auto
      intro!: skip_seq Utils_Reader_Monad_Hoare.seq
      simp add: ith_state_Suc_eq[unfolded eager_step_def])
qed

lemma threshold_exceeded_of_k_lt :
  \<open>\<turnstile>rd
    \<lbrakk>same_states\<rbrakk>
    \<langle>ith_state_then_step_1 i | ith_state (Suc i)\<rangle>
    \<lbrakk>(\<lambda> \<phi> state \<phi>' state'.
      state_k state < state_k state' \<longrightarrow>
      card (state_chi state) \<ge> threshold)\<rbrakk>\<close>
  using i_lt_length_xs
  by (auto
    intro!:
      seq ith_state_preserves_same_states skip_seq if_then_else
      Utils_Reader_Monad_Hoare.seq' Utils_Reader_Monad_Hoare.postcond_true
    simp add:
      ith_state_then_step_1_def
      ith_state_Suc_eq[unfolded eager_step_def eager_step_2_def]
      Let_def map_rd_def)

end

lemma
  fixes l coin_matrix
  assumes \<open>\<turnstile>rd
    \<lbrakk>(\<lambda> \<phi> state. \<phi> = coin_matrix \<and> state = initial_state)\<rbrakk>
    ith_state (length xs)
    \<lbrakk>(\<lambda> \<phi> state. state_k state > l)\<rbrakk>\<close>
    (is \<open>?P (length xs) (>)\<close>)
  shows
    \<open>\<exists> i < length xs. \<turnstile>rd
      \<lbrakk>(\<lambda> \<phi> state. \<phi> = coin_matrix \<and> state = initial_state)\<rbrakk>
      ith_state_then_step_1 i
      \<lbrakk>(\<lambda> \<phi> state. state_k state = l \<and> card (state_chi state) \<ge> threshold)\<rbrakk>\<close>
    (is \<open>\<exists> i. ?Q i\<close>)
proof (rule exI)
  text
    \<open>`?P` is a predicate such that `?P i R` holds iff
    after running the algorithm for `i` iterations, `R k_i l`.\<close>

  define j i where
    \<open>j \<equiv> Min {j. j \<le> length xs \<and> ?P j (>)}\<close> and
    \<open>i \<equiv> j - 1\<close>

  let ?are_initial_state = \<open>\<lambda> \<phi> state \<phi>' state'.
    \<phi> = coin_matrix \<and> \<phi> = \<phi>' \<and>
    state = initial_state \<and> state = state'\<close>

  text
    \<open>First, we make some basic observations about `i` and `j`, most importantly
    that:
    - `j` is a well defined minimum, so that `?P j (>)`.
       In other words, `j` is the smallest n such that after running the algorithm
       for j iterations, `k_n > l`.
    - `i < j`\<close>

  have \<open>?P j (>)\<close>
    by (metis (no_types, lifting) j_def Collect_empty_eq Min_in assms(1) finite_nat_set_iff_bounded_le less_or_eq_imp_le mem_Collect_eq)

  moreover have \<open>j = (LEAST j. ?P j (>))\<close>
    by (smt (verit, best) LeastI assms nle_le wellorder_Least_lemma(2) Least_Min dual_order.eq_iff finite_nat_set_iff_bounded_le j_def mem_Collect_eq)

  ultimately have \<open>i < j\<close>
    by (metis (mono_tags, lifting) i_def Utils_Reader_Monad_Hoare.skip bot_nat_0.not_eq_extremum diff_less initial_state_def ith_state_zero_eq less_zeroE simps(1) zero_less_one)

  then have [simp] : \<open>j = Suc i\<close> using i_def by linarith

  text
    \<open>Next we show that this is the `i` that we want, ie that:
    1. `i < length xs`
    2. After iteration `i`, `k_i = l`
    3. After iteration `i` and then step 1 of iteration `j = i + 1`,
       `|X_j| >= threshold`.\<close>

  have \<open>i < length xs\<close>
    using \<open>i < j\<close> \<open>j = (LEAST j. ?P j (>))\<close> assms wellorder_Least_lemma(2) by fastforce

  text
    \<open>`k_i = l` after running for `i` iterations, because:
    1. `i < j`
    2. `j` is the smallest `n` such that `k_n > l` after running for `n` iterations.
    3. `k` can only increase by at most 1 after iteration `j = i + 1`.\<close>
  moreover have \<open>?P i (=)\<close>
  proof -
    note \<open>i < j\<close> \<open>j = (LEAST j. ?P j (>))\<close> \<open>?P j (>)\<close>

    moreover have \<open>\<turnstile>rd
      \<lbrakk>?are_initial_state\<rbrakk>
      \<langle>ith_state i | ith_state j\<rangle>
      \<lbrakk>(\<lambda> \<phi> state \<phi>' state'. state_k state' \<le> Suc (state_k state))\<rbrakk>\<close>
      using ith_state_k_increases_by_at_most_one[OF \<open>i < length xs\<close>] initial_state_well_formed
      by (auto intro: precond_strengthen[where R' = same_states])

    ultimately show ?thesis
      apply (simp add: relational_hoare_triple_def hoare_triple_def rel_rd_def)
      by (metis (no_types, lifting) dual_order.strict_trans1 less_Suc_eq not_less_Least)
  qed

  moreover have \<open>\<turnstile>rd
    \<lbrakk>(\<lambda> \<phi> state. \<phi> = coin_matrix \<and> state = initial_state)\<rbrakk>
    ith_state_then_step_1 i
    \<lbrakk>(\<lambda> \<phi> state. card (state_chi state) \<ge> threshold)\<rbrakk>\<close>
  proof -
    have \<open>\<turnstile>rd
      \<lbrakk>?are_initial_state\<rbrakk>
      \<langle>ith_state_then_step_1 i | ith_state j\<rangle>
      \<lbrakk>(\<lambda> \<phi> state \<phi>' state'. state_k state < state_k state')\<rbrakk>\<close>
      using \<open>?P i (=)\<close> \<open>?P j (>)\<close>
      by (auto simp add: ith_state_then_step_1_def eager_step_1_def Let_def relational_hoare_triple_def rel_rd_def hoare_triple_def run_reader_simps)

    moreover have \<open>\<turnstile>rd
      \<lbrakk>?are_initial_state\<rbrakk>
      \<langle>ith_state_then_step_1 i | ith_state j\<rangle>
      \<lbrakk>(\<lambda> \<phi> state \<phi>' state'.
        state_k state < state_k state' \<longrightarrow>
        card (state_chi state) \<ge> threshold)\<rbrakk>\<close>
      using threshold_exceeded_of_k_lt[OF \<open>i < length xs\<close>] initial_state_well_formed
      by (auto intro: precond_strengthen[where R' = same_states])

    ultimately show ?thesis
      using initial_state_well_formed
      by (simp add: relational_hoare_triple_def hoare_triple_def rel_rd_def run_reader_simps)
    qed

  ultimately show \<open>?Q i\<close>
    unfolding eager_step_1_def ith_state_then_step_1_def Let_def
    by (auto simp add: relational_hoare_triple_def rel_rd_def hoare_triple_def run_reader_simps)
qed

end

lemma contrapos_state_k_lt_L:
  assumes "\<And>i. i < length xs \<Longrightarrow>
  (
    let st =
      run_reader (eager_algorithm (take i xs) \<bind> eager_step_1 xs i) \<phi> in
    \<not>(state_k st = L \<and> card (state_chi st) \<ge> threshold)
  )"
  shows "state_k (run_reader (eager_algorithm xs) \<phi>) \<le> L"
  using assms
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case
    by (auto simp add: eager_algorithm_def eager_step_def run_steps_def run_reader_simps initial_state_def)
next
  case ih:(snoc x xs)
  define stx where "stx \<equiv> run_reader (eager_algorithm xs) \<phi>"
  have *:"i < length xs \<Longrightarrow>
    eager_step_1 (xs @ [x]) i = eager_step_1 xs i" for i
    by (auto intro!: eager_step_cong)
  have 1: "state_k stx \<le> L"
    unfolding stx_def
    apply (intro ih(1))
    subgoal for i
      using ih(2)[of i] unfolding Let_def
      using * by auto
    done

  define sty where "sty \<equiv> run_reader (eager_step_1 (xs @ [x]) (length xs) stx) \<phi>"
  have stky: "state_k sty = state_k stx"
    unfolding sty_def
    by (auto simp add: eager_step_1_def run_reader_simps)

  from ih(2)[of "length xs"]
  have "\<not>(state_k sty = L \<and> card (state_chi sty) \<ge> threshold)"
    by (auto simp add: run_reader_simps stx_def[symmetric] sty_def[symmetric])
  
  then have "state_k sty < L \<or> state_k sty = L \<and> card (state_chi sty) < threshold"
    by (metis "1" antisym_conv1 not_le_imp_less stky)

  thus ?case
  by (auto simp add: eager_algorithm_snoc run_reader_simps stx_def[symmetric] eager_step_def sty_def[symmetric] eager_step_2_def Let_def)
qed

lemma estimate_distinct_error_bound_fail_2:
  shows "\<P>(st in
    (map_pmf
       (run_reader (eager_algorithm xs))
       (fair_bernoulli_matrix (length xs) (length xs))).
    state_k st > L) \<le> bar (length xs) L"
proof -
  have "\<P>(st in
    (map_pmf
       (run_reader (eager_algorithm xs))
       (fair_bernoulli_matrix (length xs) (length xs))).
    state_k st > L) =
  \<P>(\<phi> in fair_bernoulli_matrix (length xs) (length xs).
      state_k (run_reader (eager_algorithm xs) \<phi>) > L)"
    by auto

  (* We exceed L iff we hit a state where k = L, |X| \<ge> threshold
    after running eager_step_1.
    TODO: can this me made cleaner with only eager_algorithm? *)
  also have "... \<le>
    \<P>(\<phi> in fair_bernoulli_matrix (length xs) (length xs).
      \<exists> i < length xs. (
        let st = run_reader (eager_algorithm (take i xs) \<bind> eager_step_1 xs i) \<phi>
        in state_k st = L \<and> card (state_chi st) \<ge> threshold))"
    by (smt (verit, best) pmf_mono contrapos_state_k_lt_L mem_Collect_eq verit_comp_simplify1(3))

  (* union bound *)
  also have "... \<le> (
    \<Sum> i < length xs.
      \<P>(\<phi> in fair_bernoulli_matrix (length xs) (length xs).
        let st = run_reader (eager_algorithm (take i xs) \<bind> eager_step_1 xs i) \<phi>
        in state_k st = L \<and> card (state_chi st) \<ge> threshold))"
    proof -
      have [simp] : \<open>{\<omega>. \<exists> i < n. P i \<omega>} = (\<Union> i < n. {\<omega>. P i \<omega>})\<close>
        for n and P :: \<open>nat \<Rightarrow> 'b \<Rightarrow> bool\<close> by blast
      show ?thesis
        by (auto intro: measure_pmf.finite_measure_subadditive_finite)
    qed

  also have "... \<le> (
    \<Sum> i < length xs.
      \<P>(X in
        (map_pmf (nondet_alg_aux L (take (i+1) xs))
          (fair_bernoulli_matrix (length xs) (length xs))).
        card X \<ge> threshold))"
    apply (rule sum_mono)
    apply simp
    by (smt (verit, best) eager_algorithm_inv eager_state_inv_def eager_step_1_inv mem_Collect_eq pmf_mono run_reader_simps(3) semiring_norm(174))

  (* use a single-sided Chernoff *)
  also have "... \<le> bar (length xs) L" sorry

  finally show ?thesis by auto
qed
  
lemma estimate_distinct_error_bound_L_binom:
  shows "
    \<P>(st in
     (map_pmf
       (run_reader (eager_algorithm xs))
       (fair_bernoulli_matrix (length xs) (length xs))).
    state_k st \<le> L \<and>
      beyond_eps_range_of_card xs (compute_estimate st))
    \<le> foo (card (set xs)) L" (is "?L \<le> ?R")
proof -
  (* Splits the error event for k=0, k=1,...,k=L *)
  have "?L \<le>
    sum 
    (\<lambda>q.
    \<P>(st in
     (map_pmf
       (run_reader (eager_algorithm xs))
       (fair_bernoulli_matrix (length xs) (length xs))).
      state_k st = q \<and>
      beyond_eps_range_of_card xs (compute_estimate st)))
   {0..L}" sorry
  (* Now we go into nondeterministic *)
  also have "... \<le>
    sum 
    (\<lambda>q.
    \<P>(X in
      (map_pmf (nondet_alg_aux q xs)
         (fair_bernoulli_matrix (length xs) (length xs))).
      beyond_eps_range_of_card xs (card X * 2 ^ q)))
   {0..L}"
    sorry
  (* Go into Binomial then use Chernoff *)
  also have "... \<le>
    sum (\<lambda>q. f (card (set xs)) q) {0..L}" sorry
  also have "... \<le>
    foo (card (set xs)) L" sorry
  finally show "?thesis" .
qed

lemma estimate_distinct_error_bound:
  assumes "(L::nat) = undefined"
  shows "
    \<P>(n in estimate_distinct xs.
      n |> fail_or_satisfies (beyond_eps_range_of_card xs))
     \<le> real (length xs) / 2 ^ threshold + bar \<epsilon> thresh"
  (is "?L \<le> ?R")
proof -
  have *: "estimate_distinct_no_fail xs =
     map_pmf compute_estimate
     (map_pmf
       (run_reader (eager_algorithm xs))
       (fair_bernoulli_matrix (length xs) (length xs)))" (is "_ =  map_pmf compute_estimate ?E")   
    unfolding estimate_distinct_no_fail_eq_lazy_algo
    apply (subst eager_lazy_conversion)
    by auto

  have "?L \<le> real (length xs) / 2 ^ threshold
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
      + \<P>(st in ?E. state_k st > L)
      + \<P>(st in ?E. 
        state_k st \<le> L \<and>
          beyond_eps_range_of_card xs (compute_estimate st))"
    by (auto intro!: pmf_add)
 
  ultimately show ?thesis
    sorry
qed

end