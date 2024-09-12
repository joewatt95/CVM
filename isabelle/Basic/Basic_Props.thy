theory Basic_Props

imports
  HOL.Power
  "HOL-Probability.Product_PMF"
  "HOL-Probability.Hoeffding"
  Monad_Normalisation.Monad_Normalisation
  CVM.Basic_Algo
  CVM.Utils_Approx_Algo
  CVM.Utils_Function
  CVM.Utils_PMF
  CVM.Utils_SPMF_Hoare
  CVM.Utils_Real

begin

sledgehammer_params [
  (* verbose = true, *)
  minimize = true,
  preplay_timeout = 15,
  timeout = 60,
  max_facts = smart,
  provers = "
    cvc4 z3 verit
    e vampire spass
  "
]

locale props_basic = approx_algo + basic_algo
begin

context includes pattern_aliases
begin

(* Change p to (1 / 2 ^ k) k starting from 0 *)

definition well_formed_state :: \<open>'a state \<Rightarrow> bool\<close>
  (\<open>_ ok\<close> [20] 60) where
  \<open>state ok \<equiv> (
    let chi = state_chi state
    in finite chi \<and> card chi < threshold)\<close>

(* lemma aux :
  assumes
    \<open>state ok\<close> and
    \<open>(state_p state' = state_p state / 2) \<or> state_p state' = state_p state\<close> and
    \<open>finite (state_chi state')\<close> and
    \<open>card (state_chi state') \<le> card (state_chi state)\<close>
  shows \<open>state' ok\<close>

  using assms
  apply (cases state)
  apply (cases state')
  by auto

lemma aux' :
  fixes a :: real
  assumes
    \<open>finite y\<close> and
    \<open>x \<subseteq> y\<close> and
    \<open>card y < a\<close>
  shows \<open>card x < a\<close>
proof -
  have \<open>card x \<le> card y\<close> using assms by (auto intro!: card_mono)
  then show ?thesis using assms by auto
qed *)

context includes monad_normalisation
begin

lemma initial_state_well_formed :
  assumes \<open>card (state_chi initial_state) < threshold\<close>
  shows \<open>initial_state ok\<close>

  using assms by (simp add: initial_state_def well_formed_state_def)

lemma aux :
  assumes \<open>\<turnstile> map_pmf (\<lambda> x. if f x then Some (g x) else None) x \<Down>? y\<close>
  shows \<open>\<turnstile> spmf_of_pmf (map_pmf g x) \<Down>? y\<close>

  using assms
  by (smt (verit, del_insts) image_iff in_set_spmf option.discI pmf.set_map set_spmf_spmf_of_pmf)

(* lemma step_preserves_well_formedness :
  fixes x :: 'a
  shows \<open>\<turnstile> { well_formed_state } step x { well_formed_state } \<close>

  apply (intro hoare_triple_intro)
  apply (simp add: step_def del: bind_spmf_of_pmf map_spmf_of_pmf)
  apply (simp only: set_bind_spmf set_map_spmf)
  apply (auto simp del: bind_spmf_of_pmf map_spmf_of_pmf split: if_splits)
  apply (simp_all del: bind_spmf_of_pmf map_spmf_of_pmf add: well_formed_state_def remove_def Set.filter_def card.insert_remove)
  apply (metis card_Diff1_less card_Diff_singleton_if dual_order.strict_trans of_nat_less_iff)
  apply (metis card_Diff1_less card_Diff_singleton_if dual_order.strict_trans of_nat_less_iff)
  apply (subst (asm) aux)
  sorry *)

find_theorems "measure_pmf.prob (Pi_pmf _ _ _) _"

lemma prob_fail_step_le :
  fixes
    x :: 'a and
    state :: \<open>'a state\<close>
  shows \<open>prob_fail (step x state) \<le> 2 powr threshold\<close>

  apply (auto simp add: step_def prob_fail_def pmf_bind pmf_map split: if_splits)
  apply (smt (verit, best) divide_le_eq_1_pos divide_pos_pos gr_one_powr measure_nonneg measure_pmf.prob_le_1 mult_eq_0_iff nonzero_mult_div_cancel_left of_nat_0_le_iff zero_less_power) 
  apply (metis basic_trans_rules(21) card_insert_le insert_Diff_single of_nat_le_iff remove_def)
  apply (auto simp add: vimage_def filter_def remove_def)
  sorry

lemma prob_fail_estimate_size_le :
  fixes xs :: \<open>'a list\<close>
  assumes \<open>card (state_chi initial_state) < threshold\<close>
  shows \<open>prob_fail (estimate_size xs) \<le> length xs * 2 powr threshold\<close>
proof -
  have \<open>prob_fail (estimate_size xs) = prob_fail (run_steps initial_state xs)\<close>
    by (simp add: estimate_size_def prob_fail_def pmf_None_eq_weight_spmf)

  then show ?thesis
    using assms
    by (auto
        intro!:
          prob_fail_foldM_spmf_le initial_state_well_formed
          prob_fail_step_le step_preserves_well_formedness
        simp add: run_steps_def)
qed

end

end

end

end