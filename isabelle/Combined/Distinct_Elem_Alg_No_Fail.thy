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
    \<open>finite (state_chi state)\<close> (is \<open>finite ?chi\<close>)
    \<open>card (state_chi state) \<le> threshold\<close>
  shows
    \<open>do {
      keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
        Pi_pmf ?chi undefined \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi ?chi;

      if card chi < threshold
      then return_spmf <| state\<lparr>state_k := k + 1, state_chi := chi\<rparr>
      else fail_spmf }
    = (
      \<lblot>bernoulli_pmf <| 1 / 2\<rblot>
        |> Pi_pmf ?chi undefined
        |> map_pmf
            (\<lambda> keep_in_chi.
              if card ?chi < threshold \<or>
                restrict keep_in_chi ?chi \<noteq> restrict \<lblot>False\<rblot> ?chi
              then Some (state\<lparr>
                state_k := k + 1,
                state_chi := Set.filter keep_in_chi ?chi\<rparr>)
              else None))\<close>
proof -
  have * : \<open>\<And> b x.
    (if b then return_spmf x else fail_spmf)
      = return_pmf (if b then Some x else None)\<close>
    by (simp add: fail_spmf_def)

  have ** : \<open>\<And> keep_in_chi chi.
    restrict keep_in_chi chi = restrict \<lblot>False\<rblot> chi \<longleftrightarrow>
      (\<forall> x \<in> chi. keep_in_chi x = False)\<close>
    using restrict_ext
    by (metis (full_types) restrict_apply')

  show ?thesis
    using assms
    unfolding * **
    apply (simp add:
      fail_spmf_def Let_def
      map_pmf_def[symmetric] map_pmf_comp map_bind_pmf bind_map_pmf)
    apply (intro map_pmf_cong) apply blast
    apply (auto simp add: set_prod_pmf Set.filter_def)
    sorry
qed

lemma prob_fail_step_le :
  fixes
    x :: 'a and
    state :: \<open>'a state\<close>
  assumes \<open>state ok\<close>
  shows \<open>prob_fail (step x state) \<le> 1 / 2 ^ threshold\<close>
  using assms
  apply (auto
    simp add:
      well_formed_state_def prob_fail_def step_def
      Let_def Set.filter_def Set.remove_def fail_spmf_def
      pmf_bind pmf_map
      map_pmf_def[symmetric] map_pmf_comp map_bind_pmf bind_map_pmf)
  apply (meson basic_trans_rules(21) card_Diff1_le)
  subgoal premises prems
    using prems
    apply (subst Pi_pmf_insert')
      apply blast
      apply (metis insert_absorb)
    apply (simp add:
      map_pmf_def[symmetric] map_pmf_comp
      map_bind_pmf bind_map_pmf)
    apply (subst pmf_expectation_bind[of \<open>{True, False}\<close>])
    apply (simp_all add: image_def set_prod_pmf finite_funcset_iff)
    apply blast
    sorry
  by (meson basic_trans_rules(21) card_Diff1_le) 

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

      return_pmf <| state\<lparr>state_k := k + 1, state_chi := chi\<rparr>
    }}\<close>

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