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

fun well_formed_state :: \<open>'a state \<Rightarrow> bool\<close>
  (\<open>_ ok\<close> [20] 60) where
  \<open>\<lparr>state_p = p, state_chi = chi\<rparr> ok =
    (p \<in> {0 <.. 1} \<and> finite chi \<and> card chi < threshold)\<close>

lemma aux :
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
qed

context includes monad_normalisation
begin

lemma initial_state_well_formed :
  assumes \<open>card (state_chi initial_state) < threshold\<close>
  shows \<open>initial_state ok\<close>

  using assms by (simp add: initial_state_def)

thm well_formed_state.elims

lemma step_preserves_well_formedness :
  fixes x :: 'a
  shows \<open>\<turnstile> { well_formed_state } step x { well_formed_state } \<close>

  unfolding step_def
  apply (simp_all del: bind_spmf_of_pmf)
  apply (intro seq' [where ?Q = \<open>\<lblot>True\<rblot>\<close>])
  apply (intro postcond_true)
  apply (intro if_then_else)
  apply (intro seq'[where ?Q = \<open>\<lblot>True\<rblot>\<close>])
  apply (simp add: postcond_true)
  apply auto
  apply (intro hoare_triple_intro)
  apply (auto simp add: Set.filter_def)
  using well_formed_state.elims(2) apply fastforce 
  apply (metis basic_trans_rules(23) greaterThanAtMost_iff one_le_numeral simps(1) well_formed_state.elims(2))
  using well_formed_state.elims(2) apply fastforce
  apply (metis (no_types, lifting) aux' mem_Collect_eq select_convs(2) subsetI well_formed_state.elims(2))
  prefer 2
  apply (intro skip_intro')
  apply auto
  prefer 2
  sorry

lemma prob_fail_step_le :
  fixes
    x :: 'a and
    state :: \<open>'a state\<close>
  assumes \<open>state ok\<close>
  shows \<open>prob_fail (step x state) \<le> 2 powr threshold\<close>
proof (cases state)
  case (fields p chi)
  (*
  0 \<le> p \<le> 1 is required to simp using integral_bernoulli_pmf
  *)

  then show ?thesis
    using assms
    apply (auto simp add: prob_fail_def pmf_bind)
    (* apply (subst expectation_prod_Pi_pmf) *)
    sorry

qed

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