section \<open> Analysis of algorithm TODO \<close>
theory Algo_Transforms_No_Fail

imports
  CVM.Distinct_Elems_Algo
  CVM.Utils_SPMF_Relational
  CVM.Utils_SPMF_Hoare

begin

context with_threshold_pos
begin

definition step_no_fail ::
  \<open>'a \<Rightarrow> ('a, 'b) state_scheme \<Rightarrow> ('a, 'b) state_scheme pmf\<close> where
  \<open>step_no_fail x state \<equiv> do {
    let k = state_k state;
    let chi = state_chi state;

    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ k;

    let chi = (chi |>
      if insert_x_into_chi
      then insert x
      else Set.remove x);

    if card chi < threshold
    then return_pmf (state\<lparr>state_chi := chi\<rparr>)
    else do {
      keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
        prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi chi;

      return_pmf (state\<lparr>state_k := k + 1, state_chi := chi\<rparr>) }}\<close>

definition estimate_distinct_no_fail :: \<open>'a list \<Rightarrow> nat pmf\<close> where
  \<open>estimate_distinct_no_fail \<equiv>
    run_steps_then_estimate_pmf step_no_fail initial_state\<close>

abbreviation \<open>step_no_fail_spmf \<equiv> (\<lambda> x. spmf_of_pmf <<< step_no_fail x)\<close>

abbreviation \<open>estimate_distinct_no_fail_spmf \<equiv>
  spmf_of_pmf <<< estimate_distinct_no_fail\<close>

definition well_formed_state :: \<open>('a, 'b) state_scheme \<Rightarrow> bool\<close>
  (\<open>_ ok\<close> [20] 60) where
  \<open>state ok \<equiv> (
    let chi = state_chi state
    in finite chi \<and> card chi < threshold)\<close>

lemma well_formed_state_card_le_threshold :
  assumes \<open>state ok\<close>
  defines \<open>chi \<equiv> state_chi state\<close>
  shows
    \<open>card (Set.remove x chi) < threshold\<close>
    \<open>\<not> card (insert x chi) < threshold \<longleftrightarrow> card (insert x chi) = threshold\<close>
  using
    assms
    Diff_insert0[of x "state_chi state" "{}"]
    insert_absorb[of x "state_chi state"]
  by (fastforce simp add: well_formed_state_def Let_def Set.remove_def)+

lemma initial_state_well_formed :
  \<open>initial_state ok\<close>
  using threshold_pos by (simp add: initial_state_def well_formed_state_def)

lemma step_preserves_well_formedness :
  \<open>\<turnstile>spmf \<lbrace>well_formed_state\<rbrace> step x \<lbrace>well_formed_state\<rbrace>\<close>
  unfolding step_def bind_spmf_of_pmf[symmetric] Let_def
  by (fastforce
    intro: Utils_SPMF_Hoare.seq' hoare_tripleI
    split: if_splits
    simp add: in_set_spmf fail_spmf_def well_formed_state_def remove_def Let_def)

lemma spmf_bind_filter_chi_eq_map :
  assumes
    \<open>finite chi\<close>
    \<open>card chi \<le> threshold\<close>
  shows
    \<open>do {
      keep_in_chi \<leftarrow> prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi chi;

      if card chi < threshold
      then return_spmf <| \<kappa> chi
      else fail_spmf }
    = (
      \<lblot>bernoulli_pmf <| 1 / 2\<rblot>
        |> prod_pmf chi
        |> map_pmf (
            \<lambda> keep_in_chi.
              if card chi = threshold \<and> keep_in_chi = (\<lambda> _ \<in> chi. True)
              then None
              else Some (\<kappa> {x \<in> chi. keep_in_chi x})))\<close>
proof -
  have [simp] :
    \<open>(if b then return_spmf e else fail_spmf)
      = return_pmf (if b then Some e else None)\<close>
    for b and e :: 'c by (simp add: fail_spmf_def)

  (* This says that an indicator function keep_in_chi defined on chi,
    representing the coins we flip to throw things out, evaluates to True
    everywhere on chi if:
    1. card chi = threshold
    2. The subset of chi defined with keep_in_chi is still the same size as chi
      itself.
  *)
  have [intro] :
    \<open>keep_in_chi = (\<lambda> _ \<in> chi. True)\<close>
    if
      \<open>keep_in_chi \<in> chi \<rightarrow>\<^sub>E UNIV\<close>
      \<open>card chi = threshold\<close>
      \<open>\<not> card {x \<in> chi. keep_in_chi x} < threshold\<close>
    for keep_in_chi
    by (smt (verit, best) that assms PiE_restrict card_mono card_subset_eq mem_Collect_eq order.order_iff_strict restrict_ext subset_eq)

  have
    \<open>card {x \<in> chi. keep_in_chi x} < threshold\<close> 
    if \<open>card chi < threshold\<close> for keep_in_chi
    by (metis that assms(1) Collect_subset basic_trans_rules(21) card_mono)

  then show ?thesis
    using assms
    by (auto
      intro!: map_pmf_cong
      simp add: set_prod_pmf Let_def Set.filter_def map_pmf_def[symmetric])
qed

lemma prob_fail_step_le :
  assumes \<open>state ok\<close>
  shows \<open>prob_fail (step x state) \<le> 1 / 2 ^ threshold\<close>
  using well_formed_state_card_le_threshold[OF assms] assms
  apply (simp add: step_def well_formed_state_def Let_def)
  by (simp add:
    spmf_bind_filter_chi_eq_map prob_fail_def pmf_prod_pmf
    pmf_bind pmf_map measure_pmf_single vimage_def field_simps)

lemma prob_fail_estimate_size_le :
  \<open>prob_fail (estimate_distinct xs) \<le> length xs / 2 ^ threshold\<close>
  using prob_fail_foldM_spmf_le[OF
    step_preserves_well_formedness
    prob_fail_step_le initial_state_well_formed]
  by (fastforce simp add:
    estimate_distinct_def run_steps_then_estimate_def
    prob_fail_map_spmf_eq)

lemma step_ord_spmf_eq :
  \<open>step x state \<sqsubseteq> spmf_of_pmf (step_no_fail x state)\<close>
  by (fastforce
    intro: ord_spmf_bind_reflI
    simp add:
      step_no_fail_def step_def fail_spmf_def Let_def
      spmf_of_pmf_def bind_spmf_of_pmf[symmetric] map_bind_pmf)

lemma estimate_distinct_ord_spmf_eq :
  \<open>estimate_distinct xs \<sqsubseteq> spmf_of_pmf (estimate_distinct_no_fail xs)\<close>
  apply (simp
    del: map_spmf_of_pmf
    add:
      estimate_distinct_def estimate_distinct_no_fail_def
      run_steps_then_estimate_def
      map_spmf_of_pmf[symmetric] ord_spmf_map_spmf)
  by (metis (mono_tags, lifting) foldM_spmf_of_pmf_eq(2) foldM_spmf_ord_spmf_eq_of_ord_spmf_eq ord_pmf_increaseI ord_spmf_eq_leD step_ord_spmf_eq)

(* Think of P as event that `estimate` is the wrong count *)
theorem prob_estimate_distinct_fails_or_satisfies_le :
  \<open>\<P>(estimate in estimate_distinct xs. estimate |> fails_or_satisfies P)
  \<le> real (length xs) / 2 ^ threshold
    + \<P>(estimate in estimate_distinct_no_fail xs. P estimate)\<close>
  by (smt (verit, del_insts) Collect_cong estimate_distinct_ord_spmf_eq measure_spmf_spmf_of_pmf prob_fail_estimate_size_le prob_fails_or_satisfies_le_prob_fail_plus_prob prob_le_prob_of_ord_spmf_eq)

end

end