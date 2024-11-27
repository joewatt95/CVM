theory Distinct_Elems_While

imports
  CVM.Distinct_Elems_Algo
  CVM.Algo_Transforms_No_Fail

begin

context with_threshold
begin

definition fix_state_while :: \<open>'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>fix_state_while \<equiv> loop_spmf.while (\<lambda> state.
    card (state_chi state) = threshold) (\<lambda> state. do {
      let chi = state_chi state;

      keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
        prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi chi;
      let k = state_k state + 1;

      return_spmf \<lparr>state_k = k, state_chi = chi\<rparr>})\<close>

definition step_while :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step_while x state \<equiv> do {
    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ (state_k state);

    let chi = (state
      |> state_chi
      |> if insert_x_into_chi
        then insert x
        else Set.remove x);

    fix_state_while (state\<lparr>state_chi := chi\<rparr>) }\<close>

definition estimate_distinct_while :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_distinct_while \<equiv> run_steps_then_estimate_spmf step_while\<close>

end

context with_threshold_pos
begin

lemma aux :
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
  using assms by simp

lemma
  assumes \<open>state ok\<close>
  shows \<open>prob_fail (step_while x state) \<le> prob_fail (step x state)\<close>
proof -
  have \<open>\<turnstile>pmf
    \<lbrakk>(\<lambda> state state'. state = state' \<and> (state ok))\<rbrakk>
    \<langle>step x | step_while x\<rangle>
    \<lbrakk>ord_option (=)\<rbrakk>\<close>
    (is \<open>\<turnstile>pmf \<lbrakk>?R\<rbrakk> \<langle>_ | _ \<rangle> \<lbrakk>_\<rbrakk>\<close>)
    unfolding step_def step_while_def Let_def Set.filter_def Set.remove_def 
    apply (rule Utils_PMF_Relational.seq'[where S = \<open>(=)\<close>])
    apply (simp add: Utils_PMF_Relational.relational_hoare_triple_def pmf.rel_refl)
    apply (subst aux)
    using assms
    apply (auto simp add: well_formed_state_def Let_def card_insert_if)
    apply (rule Utils_PMF_Relational.if_then_else)
    apply simp_all
    apply (rule Utils_PMF_Relational.seq'[where S = \<open>(=)\<close>])
    by (auto
      simp add: aux Set.filter_def fail_spmf_def Utils_PMF_Relational.relational_hoare_triple_def pmf.rel_refl)

  then show ?thesis
    using assms by (blast intro: prob_fail_le_of_relational_hoare_triple)
qed

end

end