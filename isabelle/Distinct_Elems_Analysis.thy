section \<open> TODO \<close>
theory Distinct_Elems_Analysis

imports
  CVM.Distinct_Elems_Algo
  CVM.Distinct_Elems_No_Fail
  CVM.Distinct_Elems_Eager
  CVM.Distinct_Elems_Nondet
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

thm eager_algorithm_snoc

(* eager_algorithm (?xs @ [?x])
= eager_algorithm ?xs \<bind> eager_step (?xs @ [?x]) (length ?xs) *)

lemma eager_algorithm_take_eq :
  assumes \<open>i < length xs\<close>
  shows
    \<open>eager_algorithm (take (i + 1) xs) =
      eager_algorithm (take i xs) \<bind> eager_step (take (i + 1) xs) i\<close>
  using assms
  by (simp add: take_Suc_conv_app_nth eager_algorithm_snoc)

lemma aux :
  \<open>state_k state \<le> state_k (run_reader (eager_step xs i state) \<phi>)\<close>
  by (simp add:
    eager_step_def eager_step_1_def eager_step_2_def
    run_reader_simps Let_def)

(* k increases monotonically across iterations. *)
lemma aux' :
  assumes \<open>i < length xs\<close>
  shows
    \<open>state_k (run_eager_algorithm (take i xs) \<phi>)
    \<le> state_k (run_eager_algorithm (take (i + 1) xs) \<phi>)\<close>
  by (metis assms aux eager_algorithm_take_eq run_reader_simps(3))

lemma
  assumes \<open>i + j \<le> length xs\<close>
  shows
    \<open>state_k (run_eager_algorithm (take i xs) \<phi>)
    \<le> state_k (run_eager_algorithm (take (i + j) xs) \<phi>)\<close>
  apply (induction j)
  apply simp
  by (metis (no_types, opaque_lifting) One_nat_def add_Suc_right aux' leI le_simps(3) le_trans nat_le_linear semiring_norm(51) take_all_iff)

(* k is incremented iff we flip H for the new element and hit the threshold upon
inserting it. *)
lemma
  fixes \<phi> xs
  defines
    \<open>state i \<equiv>
      flip run_reader \<phi> (do {
        state \<leftarrow> eager_algorithm <| take i xs;
        eager_step_1 xs i state })\<close>
  shows
    \<open>state_k (state <| i + 1) = state_k (state i)
    \<longleftrightarrow> (
      card (state_chi (state i)) + 1 = threshold \<and>
      (\<forall> k' < state_k (state i). curry \<phi> k' i) \<and>
      card (state_chi <| state <| i + 1) = threshold)\<close>
  sorry

lemma
  assumes \<open>state_k (run_eager_algorithm xs \<phi>) > L\<close>
  defines
    \<open>state i \<equiv>
      flip run_reader \<phi> (do {
        state \<leftarrow> eager_algorithm <| take i xs;
        eager_step_1 xs i state })\<close>
  obtains i where
    \<open>state_k (state i) = L\<close>
    \<open>card (state_chi <| state i) = threshold\<close>
   (* See personal (Joe), written notes for sketch of the proof here. *)
  sorry

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
      then show ?thesis
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