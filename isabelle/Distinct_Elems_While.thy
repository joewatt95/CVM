theory Distinct_Elems_While

imports
  CVM.Distinct_Elems_Algo
  CVM.Algo_Transforms_No_Fail
  CVM.Utils_PMF_Bernoulli_Binomial

begin

context with_threshold
begin

definition cond :: \<open>'a state \<Rightarrow> bool\<close> where
  \<open>cond \<equiv> \<lambda> state. card (state_chi state) = threshold\<close>

definition body :: \<open>'a state \<Rightarrow> 'a state pmf\<close> where
 \<open>body \<equiv> \<lambda> state. do {
  let chi = state_chi state;

  keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
    prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

  let chi = Set.filter keep_in_chi chi;
  let k = state_k state + 1;

  return_pmf \<lparr>state_k = k, state_chi = chi\<rparr>}\<close>

abbreviation \<open>body_spmf \<equiv> spmf_of_pmf <<< body\<close>

definition step_while :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step_while x state \<equiv> do {
    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ (state_k state);

    let chi = (state
      |> state_chi
      |> if insert_x_into_chi
        then insert x
        else Set.remove x);

    loop_spmf.while cond body_spmf (state\<lparr>state_chi := chi\<rparr>) }\<close>

definition estimate_distinct_while :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_distinct_while \<equiv> run_steps_then_estimate_spmf step_while\<close>
end

context with_threshold_pos
begin

lemma lossless_step_while_loop [simp] :
  \<open>lossless_spmf <| loop_spmf.while cond body_spmf state\<close>
proof -
  have
    \<open>{keep_in_chi. card (Set.filter keep_in_chi chi) = card chi} =
      chi \<rightarrow> {True}\<close>
    if \<open>finite chi\<close> for chi :: \<open>'a set\<close>
    using that
    apply (intro Set.set_eqI)
    apply (simp add: Pi_iff)
    by (metis card_mono card_seteq finite_filter member_filter subsetI)

  with threshold_pos have
    \<open>\<P>(state in body state. cond state) = 1 / 2 ^ threshold\<close>
    if \<open>cond state\<close> for state :: \<open>'a state\<close>
    using that
    by (fastforce simp add:
      cond_def body_def card_ge_0_finite Let_def vimage_def field_simps
      map_pmf_def[symmetric] measure_Pi_pmf_Pi measure_pmf_single)

  then show ?thesis
    by (auto
      intro: loop_spmf.termination_0_1_immediate
      simp add: pmf_map_pred_true_eq_prob pmf_False_conv_True threshold_pos)
qed

lemma lossless_step_while [simp] :
  \<open>lossless_spmf <| step_while x state\<close>
  by (simp add: step_while_def)

lemma lossless_estimate_distinct_while [simp] :
  \<open>lossless_spmf <| estimate_distinct_while xs\<close>
  by (simp add: estimate_distinct_while_def run_steps_then_estimate_def)

lemma
  \<open>\<bar>\<P>(x in measure_spmf <| estimate_distinct_while xs. P x)
    - \<P>(x in measure_spmf <| estimate_distinct xs. P x)\<bar>
  \<le> length xs / 2 ^ threshold\<close>
  apply (induction xs)
  apply (simp_all add:
    estimate_distinct_while_def estimate_distinct_def run_steps_then_estimate_def
    step_def step_while_def initial_state_def
    measure_map_spmf vimage_def space_measure_spmf Let_def)
  unfolding Let_def Set.filter_def Set.remove_def if_distribR
  sorry

(* lemma aux :
  fixes state
  defines \<open>chi \<equiv> state_chi state\<close>
  assumes \<open>finite chi\<close> \<open>card chi \<le> threshold\<close>
  shows
    \<open>fix_state_while state = (
      if card (state_chi state) < threshold
      then return_spmf state
      else do {
        keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
          prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

        let chi = Set.filter keep_in_chi chi;
        let k = state_k state + 1;

        fix_state_while \<lparr>state_k = k, state_chi = chi\<rparr> } )\<close>
  unfolding fix_state_while_def Let_def
  apply (subst bind_spmf_of_pmf[symmetric])+
  apply (subst loop_spmf.while.simps)
  apply (subst bind_spmf_assoc)
  using assms by simp *)

(* thm SPMF.fundamental_lemma[
  where p = \<open>spmf_of_pmf (step_no_fail x state)\<close>,
  where q = \<open>step_while x state\<close>,
  where A = P, where B = P,
  of
    \<open>\<lambda> state'. card (state_chi state') \<ge> threshold\<close>
    (* \<open>\<lambda> state'. state_k state' > state_k state + 1\<close> *)
] *)

end

end