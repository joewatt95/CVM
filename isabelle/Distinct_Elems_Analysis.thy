section \<open> TODO \<close>
theory Distinct_Elems_Analysis

imports
  CVM.Distinct_Elems_Algo
  CVM.Distinct_Elems_No_Fail
  CVM.Distinct_Elems_Eager
  CVM.Distinct_Elems_Nondet
begin

context with_threshold
begin

context
  fixes \<epsilon> :: real
  assumes eps_pos : \<open>\<epsilon> > 0\<close>
begin

lemma estimate_distinct_errror_bound_fail_2:
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
  also have "... =
    measure_pmf.prob (fair_bernoulli_matrix (length xs) (length xs))
    {\<phi>. state_k (run_reader (eager_algorithm xs) \<phi>) > L}
    " by auto
  
  (* We exceed L iff we hit a state where k = L, |X| \<ge> threshold
    after running eager_step_1.
    TODO: can this me made cleaner with only eager_algorithm? *)
  also have "... =
    measure_pmf.prob (fair_bernoulli_matrix (length xs) (length xs))
    (\<Union>i\<in>{0..length xs}.
      {\<phi>.
      let st = run_reader (eager_algorithm (take i xs) \<bind> eager_step_1 xs i) \<phi> in
      state_k st = L \<and> card (state_chi st) \<ge> threshold})"
    apply (intro measure_pmf_cong)
    apply auto
    sorry

  (* union bound *)
  also have "... \<le>
    (\<Sum>i\<in>{0..length xs}.
    measure_pmf.prob (fair_bernoulli_matrix (length xs) (length xs))
      {\<phi>.
      let st = run_reader (eager_algorithm (take i xs) \<bind> eager_step_1 xs i) \<phi> in
      state_k st = L \<and> card (state_chi st) \<ge> threshold})
    " sorry
  also have "... =
    (\<Sum>i\<in>{0..length xs}.
    \<P>(X in
      (map_pmf (nondet_alg_aux L (take i xs))
         (fair_bernoulli_matrix (length xs) (length xs))).
      card X \<ge> threshold))"
    sorry
  (* use a single-sided Chernoff *)
  also have "... \<le> bar (length xs) L" sorry
  finally show ?thesis by auto
qed
  
lemma estimate_distinct_errror_bound_L_binom:
  shows "
    \<P>(st in
     (map_pmf
       (run_reader (eager_algorithm xs))
       (fair_bernoulli_matrix (length xs) (length xs))).
    state_k st \<le> L \<and>
      beyond_eps_range_of_card \<epsilon> xs (compute_estimate st))
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
      beyond_eps_range_of_card \<epsilon> xs (compute_estimate st)))
   {0..L}" sorry
  (* Now we go into nondeterministic *)
  also have "... \<le>
    sum 
    (\<lambda>q.
    \<P>(X in
      (map_pmf (nondet_alg_aux q xs)
         (fair_bernoulli_matrix (length xs) (length xs))).
      beyond_eps_range_of_card \<epsilon> xs (card X * 2 ^ q)))
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
      n |> fail_or_satisfies (beyond_eps_range_of_card \<epsilon> xs))
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
       n |> (beyond_eps_range_of_card \<epsilon> xs))"
    by (intro prob_estimate_distinct_fail_or_satisfies_le)
  
  moreover have "... =
    real (length xs) / 2 ^ threshold
      + \<P>(st in ?E.
        beyond_eps_range_of_card \<epsilon> xs (compute_estimate st))"
    unfolding *
    by auto
  moreover have "... \<le>
    real (length xs) / 2 ^ threshold
      + \<P>(st in ?E. state_k st > L)
      + \<P>(st in ?E. 
        state_k st \<le> L \<and>
          beyond_eps_range_of_card \<epsilon> xs (compute_estimate st))"
    by (auto intro!: pmf_add)
 
  ultimately show ?thesis
    sorry
qed

end

end

end