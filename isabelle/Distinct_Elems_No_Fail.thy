section \<open> Analysis of algorithm TODO \<close>
theory Distinct_Elems_No_Fail

imports
  CVM.Distinct_Elems_Algo
  CVM.Utils_PMF_Common
  CVM.Utils_SPMF_FoldM
  CVM.Utils_SPMF_Rel
  CVM.Utils_SPMF_Hoare

begin

context with_threshold
begin

definition step_no_fail :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state pmf\<close> where
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
        Pi_pmf chi undefined \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi chi;

      return_pmf \<lparr>state_k = k + 1, state_chi = chi\<rparr> }}\<close>

definition estimate_distinct_no_fail :: \<open>'a list \<Rightarrow> nat pmf\<close> where
  \<open>estimate_distinct_no_fail \<equiv> run_steps_then_estimate_pmf step_no_fail\<close>

definition well_formed_state :: \<open>'a state \<Rightarrow> bool\<close>
  (\<open>_ ok\<close> [20] 60) where
  \<open>state ok \<equiv> (
    let chi = state_chi state
    in finite chi \<and> card chi < threshold)\<close>

lemma initial_state_well_formed :
  \<open>initial_state ok\<close>
  using threshold_pos by (simp add: initial_state_def well_formed_state_def)

lemma step_preserves_well_formedness :
  \<open>\<turnstile> \<lbrace>well_formed_state\<rbrace> step x \<lbrace>well_formed_state\<rbrace>\<close>
  unfolding step_def bind_spmf_of_pmf[symmetric] Let_def
  by (fastforce
    intro: seq' hoare_tripleI
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

    This is marked as an intro pattern, ie a derived introduction rule, to
    assist classical sequent calculi based proof search procedures like auto to
    prove that not filtering anything out of chi is equivalent to sampling a
    keep_in_chi that is True everywhere on chi.
    The forward direction can be difficult for such procedures, as this
    involves reasoning about set and subset cardinalities.
    Note that we also use intro! instead of just intro, because we want to
    override other more general intro patterns, like function extensionality.
  *)
  have [intro!] :
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
      intro: map_pmf_cong
      simp add: set_prod_pmf Let_def Set.filter_def map_pmf_def[symmetric])
qed

lemma prob_fail_step_le :
  assumes \<open>state ok\<close>
  shows \<open>prob_fail (step x state) \<le> 1 / 2 ^ threshold\<close>
proof -
  let ?chi = \<open>state_chi state\<close>
  let ?chi' = \<open>insert x ?chi\<close>

  have \<open>card (Set.remove x ?chi) < threshold\<close>
    by (metis assms card_Diff1_less card_Diff_singleton_if dual_order.strict_trans remove_def well_formed_state_def) 

  moreover have \<open>\<not> card ?chi' < threshold \<longleftrightarrow> card ?chi' = threshold\<close>
    by (metis Suc_leI assms card.insert insert_absorb le_neq_implies_less nat_neq_iff well_formed_state_def)

  (* This inequality arises because assuming that |chi| = threshold - 1,
    LHS = probability of failure at iteration i
        = (prob of sampling H (and hence inserting x into chi)
            with probability 1 / 2 ^ k)
          * (prob of not throwing anything away in chi afterwards) *)
  moreover have
    \<open>((1 :: real) / 2) ^ threshold / 2 ^ k \<le> 1 / 2 ^ threshold\<close> for threshold k
    by (metis div_by_1 frac_le dual_order.order_iff_strict half_gt_zero_iff power_one_over two_realpow_ge_one verit_comp_simplify(28) zero_less_power)

  ultimately show ?thesis
    using assms
    apply (simp add: step_def well_formed_state_def Let_def)
    by (simp add:
      spmf_bind_filter_chi_eq_map prob_fail_def pmf_prod_pmf
      pmf_bind pmf_map measure_pmf_single vimage_def)
qed

lemma prob_fail_estimate_size_le :
  \<open>prob_fail (estimate_distinct xs) \<le> length xs / 2 ^ threshold\<close>
  using prob_fail_foldM_spmf_le[OF
    step_preserves_well_formedness
    prob_fail_step_le initial_state_well_formed]
  by (fastforce simp add:
    estimate_distinct_def run_steps_then_estimate_def run_steps_def
    prob_fail_map_spmf_eq)

lemma step_ord_spmf_eq :
  \<open>ord_spmf (=) (step x state) (spmf_of_pmf <| step_no_fail x state)\<close>
  by (fastforce
    intro: ord_spmf_bind_reflI
    simp add:
      step_no_fail_def step_def fail_spmf_def Let_def
      spmf_of_pmf_def bind_spmf_of_pmf[symmetric] map_bind_pmf)

lemma estimate_distinct_ord_spmf_eq :
  \<open>ord_spmf (=)
    (estimate_distinct xs)
    (spmf_of_pmf <| estimate_distinct_no_fail xs)\<close>
  apply (simp
    del: map_spmf_of_pmf
    add:
      estimate_distinct_def estimate_distinct_no_fail_def
      run_steps_then_estimate_def run_steps_def
      map_spmf_of_pmf[symmetric] ord_spmf_map_spmf)
  by (metis (mono_tags, lifting) foldM_spmf_ord_spmf_eq_of_ord_spmf_eq ord_pmf_increaseI ord_spmf_eq_leD spmf_of_pmf_foldM_pmf_eq_foldM_spmf with_threshold.step_ord_spmf_eq with_threshold_axioms) 

(* Think of P as event that est is the wrong count *)
theorem prob_estimate_distinct_fail_or_satisfies_le :
  \<open>\<P>(est in estimate_distinct xs. est |> fail_or_satisfies P)
    \<le> real (length xs) / 2 ^ threshold
      + \<P>(est in estimate_distinct_no_fail xs. P est)\<close>
  by (smt (verit, del_insts) Collect_cong estimate_distinct_ord_spmf_eq measure_spmf_spmf_of_pmf prob_fail_estimate_size_le prob_fail_or_satisfies_le_prob_fail_plus_prob prob_le_prob_of_ord_spmf_eq)

end

end