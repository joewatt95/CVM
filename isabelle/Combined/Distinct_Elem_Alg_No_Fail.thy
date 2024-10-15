section \<open> Analysis of algorithm TODO \<close>
theory Distinct_Elem_Alg_No_Fail

imports
  Distinct_Elem_Alg
  CVM.Utils_PMF
  CVM.Utils_SPMF_FoldM
  CVM.Utils_SPMF_Rel
  CVM.Utils_SPMF_Hoare
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

context with_threshold
begin

definition well_formed_state :: \<open>('a, 'b) state_scheme \<Rightarrow> bool\<close>
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
    intro: seq' hoare_triple_intro
    split: if_splits
    simp add: in_set_spmf fail_spmf_def well_formed_state_def remove_def Let_def)

lemma aux :
  assumes
    \<open>finite chi\<close> and
    \<open>card chi \<le> threshold\<close>
  shows
    \<open>do {
      keep_in_chi \<leftarrow> prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi chi;

      if card chi < threshold
      then return_spmf <| ctx chi
      else fail_spmf }
    = (
      \<lblot>bernoulli_pmf <| 1 / 2\<rblot>
        |> prod_pmf chi
        |> map_pmf (
            \<lambda> keep_in_chi.
              if card chi = threshold \<and> keep_in_chi = (\<lambda> _ \<in> chi. True)
              then None
              else Some (ctx {x \<in> chi. keep_in_chi x})))\<close>
proof -
  have * : \<open>\<And> b e.
    (if b then return_spmf e else fail_spmf)
      = return_pmf (if b then Some e else None)\<close>
    by (simp add: fail_spmf_def)

  have ** : \<open>\<And> p.
    \<lbrakk>card chi = threshold;
      p \<in> chi \<rightarrow>\<^sub>E UNIV;
      \<not> card {a \<in> chi. p a} < threshold\<rbrakk>
    \<Longrightarrow> p = (\<lambda> x \<in> chi. True)\<close>
    by (smt (verit, best) assms PiE_restrict card_mono card_subset_eq mem_Collect_eq order.order_iff_strict restrict_ext subset_eq)

  have \<open>\<And> p.
    card chi < threshold \<Longrightarrow> card {x \<in> chi. p x} < threshold\<close>
    using assms by (metis Collect_subset basic_trans_rules(21) card_mono)

  then show ?thesis using assms by (auto
    intro!: map_pmf_cong **
    simp add: * set_prod_pmf Let_def Set.filter_def map_pmf_def[symmetric])
qed
(* 
find_theorems "measure_pmf.prob" "Pi_pmf"

find_theorems "_(_ := _)" "restrict"

find_theorems "insert _ _ \<rightarrow>\<^sub>E _"

find_theorems "_ \<in> Pi _ _" *)

lemma prob_fail_step_le :
  assumes \<open>state ok\<close>
  shows \<open>prob_fail (step x state) \<le> 1 / 2 ^ threshold\<close>
proof-
  show ?thesis
    using assms
    apply (simp add: prob_fail_def step_def well_formed_state_def Let_def)
    apply (subst aux)
    apply (simp_all add: remove_def)
    apply (metis Suc_leI card_Diff1_le card_insert_disjoint dual_order.trans insert_absorb le_simps(1))
    apply (auto simp add: pmf_bind pmf_map vimage_def Set.remove_def card.insert_remove)

    subgoal
      apply (subst Pi_pmf_insert')
      apply (simp_all add: assms well_formed_state_def Let_def)
      apply (metis card.remove)

      apply (simp add:
        measure_bind_pmf vimage_def
        map_pmf_def[symmetric] map_bind_pmf bind_map_pmf)

      apply (cases \<open>x \<in> state_chi state\<close>)

      subgoal premises prems
        proof -
          have False
            using card_Diff1_less prems(1) prems(2) prems(3) prems(5) by fastforce 
          then show ?thesis by blast
        qed

      subgoal premises prems
        proof -
          (* have
            \<open>{p. p(x := True) = (\<lambda> _ \<in> insert x (state_chi state). True)}
              = (\<Pi> y \<in> insert x (state_chi state).
                  if y = x then UNIV else {True})\<close>
            using assms prems
            apply (auto simp add: well_formed_state_def Let_def)
            apply (metis array_rules(2) insert_iff restrict_apply)
            sorry *)

          have
            \<open>{p. p(x := False) = (\<lambda> _ \<in> insert x (state_chi state). True)} = {}\<close>
            by (smt (verit) Collect_empty_eq fun_upd_same insertI1 restrict_apply') 

          then show ?thesis
            using assms prems
            apply auto
            sorry
        qed
      done

  by (meson basic_trans_rules(21) card_Diff1_le)
qed

lemma prob_fail_map_spmf:
  "prob_fail (map_spmf f p) = prob_fail p"
  unfolding prob_fail_def by (simp add: pmf_None_eq_weight_spmf)

lemma prob_fail_estimate_size_le :
  \<open>prob_fail (estimate_distinct xs) \<le> length xs / 2 ^ threshold\<close>
  using prob_fail_foldM_spmf_le[OF
    step_preserves_well_formedness
    prob_fail_step_le initial_state_well_formed]
  by (fastforce simp add: estimate_distinct_def prob_fail_map_spmf run_steps_def)

definition step_nf :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_nf x state \<equiv> do {
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

      return_pmf <| state\<lparr>state_k := k + 1, state_chi := chi\<rparr> }}\<close>

definition run_steps_nf :: \<open>'a state \<Rightarrow> 'a list \<Rightarrow> 'a state pmf\<close> where
  \<open>run_steps_nf \<equiv> flip (foldM_pmf step_nf)\<close>

definition estimate_distinct_nf :: \<open>'a list \<Rightarrow> nat pmf\<close> where
  \<open>estimate_distinct_nf \<equiv>
    run_steps_nf initial_state >>>
      map_pmf (\<lambda>state. card (state_chi state) * 2 ^ (state_k state))\<close>

lemma step_ord_spmf_eq :
  \<open>ord_spmf (=) (step x state) (spmf_of_pmf <| step_nf x state)\<close>
  by (fastforce
    intro: ord_spmf_bind_reflI
    simp add:
      step_nf_def step_def fail_spmf_def Let_def
      spmf_of_pmf_def bind_spmf_of_pmf[symmetric] map_bind_pmf)

find_theorems "spmf_of_pmf" "map_pmf"

lemma estimate_distinct_ord_spmf_eq :
  \<open>ord_spmf (=)
    (estimate_distinct xs)
    (spmf_of_pmf <| estimate_distinct_nf xs)\<close>
  apply (simp
    del: map_spmf_of_pmf
    add:
      estimate_distinct_def run_steps_def
      estimate_distinct_nf_def run_steps_nf_def
      map_spmf_of_pmf[symmetric]
      ord_spmf_map_spmf)
  by (metis (mono_tags, lifting) foldM_spmf_ord_spmf_eq_of_ord_spmf_eq ord_pmf_increaseI ord_spmf_eq_leD spmf_of_pmf_foldM_pmf_eq_foldM_spmf with_threshold.step_ord_spmf_eq with_threshold_axioms) 

(* Think of P as event that res is the wrong count *)
lemma prob_estimate_distinct_le :
  \<open>\<P>(res in measure_spmf <| estimate_distinct xs. P res)
    \<le> \<P>(res in estimate_distinct_nf xs. P res)\<close>
  using estimate_distinct_ord_spmf_eq prob_le_prob_of_ord_spmf_eq by fastforce

lemma prob_estimate_distinct_fail_or_satisfies_le :
  shows
    \<open>\<P>(state in estimate_distinct xs. state |> fail_or_satisfies P)
      \<le> real (length xs) / 2 ^ threshold
        + \<P>(state in estimate_distinct_nf xs. P state)\<close>
  by (smt (verit, best) Collect_cong prob_estimate_distinct_le prob_fail_estimate_size_le prob_fail_or_satisfies_le_prob_fail_plus_prob) 

end
end