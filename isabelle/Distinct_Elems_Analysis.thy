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

sledgehammer_params [
  (* verbose *)
  minimize = true,
  preplay_timeout = 15,
  timeout = 60,
  max_facts = smart,
  provers = "
    cvc4 z3 verit
    e vampire spass
  "
]

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

lemma eager_step_preserves_well_formedness :
  \<open>\<turnstile>rd \<lbrakk>finite_state_chi\<rbrakk> eager_step xs i \<lbrakk>finite_state_chi\<rbrakk>\<close>
  unfolding eager_step_def eager_step_1_def eager_step_2_def Let_def map_rd_def
  by (fastforce
    intro:
      Utils_Reader_Monad_Hoare.seq'[where Q = finite_state_chi]
      Utils_Reader_Monad_Hoare.seq'[where Q = \<open>\<lblot>\<lblot>True\<rblot>\<rblot>\<close>] if_then_else postcond_true
    simp add: remove_def)

context
  fixes
    i :: nat and
    xs :: \<open>'a list\<close>
  assumes i_lt_length_xs : \<open>i < length xs\<close>
begin

definition \<open>ith_state j \<equiv> foldM_rd (eager_step (take j xs)) [0 ..< j]\<close>

lemma ith_state_preserves_same_states :
  \<open>\<turnstile>rd \<lbrakk>same_states\<rbrakk> \<langle>ith_state i | ith_state i\<rangle> \<lbrakk>same_states\<rbrakk>\<close>
  using i_lt_length_xs ith_state_def
  by (smt (verit, best)
    Utils_Reader_Monad_Hoare.loop_unindexed eager_step_preserves_well_formedness
    Utils_Reader_Monad_Hoare.hoare_tripleE Utils_Reader_Monad_Relational.relational_hoare_triple_def rel_rd_def)

lemma
  defines
    \<open>S j \<phi> state \<phi>' state' \<equiv>
      \<phi> = \<phi>' \<and> finite_state_chi \<phi> state \<and> finite_state_chi \<phi> state' \<and>
      card (state_chi state') = Suc (card <| state_chi state)
      \<longleftrightarrow> (\<forall> k' < state_k state. curry \<phi> k' j) \<and>
          (state_chi state' = insert (xs ! j) (state_chi state)) \<and>
          xs ! j \<notin> state_chi state\<close>
  assumes \<open>i < length xs\<close>
  shows \<open>\<turnstile>rd
    \<lbrakk>same_states\<rbrakk>
    \<langle>ith_state i | ith_state i >=> eager_step_1 xs i\<rangle>
    \<lbrakk>S i\<rbrakk>\<close>
proof -
  note ith_state_preserves_same_states

  moreover have
    \<open>\<turnstile>rd \<lbrakk>same_states \<phi> state\<rbrakk> eager_step_1 xs i \<lbrakk>S i \<phi> state\<rbrakk>\<close> for \<phi> state 
    unfolding
      assms eager_step_1_def Let_def Set.remove_def
      map_rd_def[symmetric] map_bind_rd map_comp_rd
    unfolding map_rd_def
    using card_Diff1_le[of \<open>state_chi state\<close> \<open>xs ! i\<close>]
    by (fastforce
      intro: Utils_Reader_Monad_Hoare.seq'[where Q = \<open>\<lambda> \<phi>' state'. \<phi> = \<phi>' \<and> \<phi> = state'\<close>]
      simp add: Utils_Reader_Monad_Hoare.hoare_triple_def get_rd_def insert_absorb)

  ultimately show ?thesis by (blast intro: skip_seq)
qed

lemma ith_state_Suc_eq :
  \<open>ith_state (Suc i) = (ith_state i >=> eager_step (take (Suc i) xs) i)\<close>
  using i_lt_length_xs
  by (fastforce
    intro: arg_cong2[where f = bind_rd] foldM_cong eager_step_cong
    simp add: ith_state_def foldM_rd_snoc take_Suc_conv_app_nth)

lemma
  \<open>\<turnstile>rd
    \<lbrakk>same_states\<rbrakk>
    \<langle>ith_state i | ith_state (Suc i)\<rangle>
    \<lbrakk>(\<lambda> _ state _ state'. state_k state \<le> state_k state')\<rbrakk>\<close>
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
      \<lbrakk>(\<lambda> _ state'. state_k state \<le> state_k state')\<rbrakk>\<close>
    for \<phi> state i and xs :: \<open>'a list\<close>
    unfolding eager_step_1_def eager_step_2_def Let_def map_rd_def
    by (auto intro!: Utils_Reader_Monad_Hoare.seq' if_then_else postcond_true)

  ultimately show ?thesis
    apply (simp add: i_lt_length_xs ith_state_Suc_eq)
    unfolding eager_step_def
    by (blast intro: skip_seq Utils_Reader_Monad_Hoare.seq)
qed

(* k is incremented iff we flip H for the new element and hit the threshold upon
inserting it. *)

lemma
  fixes \<phi>
  defines \<open>state j \<equiv> run_eager_algorithm (take j xs) \<phi>\<close>
  shows
    \<open>i < length xs \<Longrightarrow>
    state_k (state <| Suc i) > state_k (state i)
    \<longleftrightarrow> (
      Suc (card <| state_chi <| state i) = threshold \<and>
      (\<forall> k' < state_k (state i). curry \<phi> k' i))\<close>
  (* using assms aux'
  unfolding
    eager_algorithm_take_eq
    eager_algorithm_def
    eager_step_def eager_step_1_def eager_step_2_def Let_def
    run_reader_simps Set.filter_def remove_def
  apply (auto split: if_splits) *)
  sorry

lemma
  assumes \<open>state_k (run_eager_algorithm xs \<phi>) > L\<close>
  defines
    \<open>state j \<equiv>
      flip run_reader \<phi> (do {
        state \<leftarrow> eager_algorithm <| take j xs;
        eager_step_1 xs j state })\<close>
  obtains j where
    \<open>state_k (state j) = L\<close>
    \<open>card (state_chi <| state j) = threshold\<close>
  sorry

end

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
  also have "... =
    \<P>(\<phi> in fair_bernoulli_matrix (length xs) (length xs).
      \<exists> i < length xs. (
        let st = run_reader (eager_algorithm (take i xs) \<bind> eager_step_1 xs i) \<phi>
        in state_k st = L \<and> card (state_chi st) \<ge> threshold))"
    proof -
      have
        \<open>eager_state_inv (take (i + 1) xs) \<phi> <|
          run_reader (eager_algorithm (take i xs) \<bind> eager_step_1 xs i) \<phi>\<close>
        if \<open>i < length xs\<close> for i \<phi>
        by (metis eager_algorithm_inv eager_step_1_inv run_reader_simps(3) that) 

      then show ?thesis
        apply (intro measure_pmf_cong)
        (* using eager_step_inv eager_step_1_inv *)
        apply (auto simp add:
          eager_state_inv_def nondet_alg_aux_def
          bernoulli_matrix_def set_Pi_pmf)
        sorry
    qed

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

  also have "... = (
    \<Sum> i \<le> length xs.
      \<P>(X in
        (map_pmf (nondet_alg_aux L (take i xs))
          (fair_bernoulli_matrix (length xs) (length xs))).
        card X \<ge> threshold))"
    sorry

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

end