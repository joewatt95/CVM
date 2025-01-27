theory CVM_Algo_Lazy_Eager

imports
  CVM_Algo_No_Fail

begin

context cvm_algo
begin

context
  fixes xs :: \<open>'a list\<close> and i :: nat
begin

definition step_1_lazy :: \<open>'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_1_lazy \<equiv> \<lambda> state. do {
    let k = state_k state; let chi = state_chi state;

    insert_x_into_chi \<leftarrow> bernoulli_pmf (f ^ k);

    let chi = (chi |>
      if insert_x_into_chi
      then insert (xs ! i)
      else Set.remove (xs ! i));

    return_pmf (state \<lparr>state_chi := chi\<rparr>) }\<close>

definition step_2_lazy :: \<open>'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_2_lazy \<equiv> \<lambda> state. do {
    let k = state_k state; let chi = state_chi state;

    if card chi = threshold then do {
      keep_in_chi \<leftarrow> prod_pmf chi (\<lambda> _. bernoulli_pmf f);
      return_pmf \<lparr>state_k = k + 1, state_chi = Set.filter keep_in_chi chi\<rparr> }
    else return_pmf (state \<lparr>state_chi := chi\<rparr>) }\<close>

definition step_lazy :: \<open>'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_lazy \<equiv> \<lambda> state. step_1_lazy state \<bind> step_2_lazy\<close>

lemmas step_1_lazy_def' = step_1_lazy_def[
  simplified map_pmf_def[symmetric] Let_def if_distribR]

lemmas step_2_lazy_def' = step_2_lazy_def[
  simplified map_pmf_def[symmetric] Let_def]

end

abbreviation
  \<open>run_steps_lazy \<equiv> \<lambda> xs. foldM_pmf (step_lazy xs) [0 ..< length xs]\<close>

lemma step_lazy_cong :
  assumes "xs ! i = ys ! i"
  shows "step_lazy xs i = step_lazy ys i"
  unfolding step_lazy_def step_1_lazy_def step_2_lazy_def
  using assms by (simp cong: if_cong)

lemma run_steps_lazy_snoc :
  \<open>run_steps_lazy (xs @ [x]) state =
    run_steps_lazy xs state \<bind> step_lazy (xs @ [x]) (length xs)\<close>
  apply (simp add: upt_Suc_append foldM_pmf_snoc)
  apply (intro bind_pmf_cong foldM_cong step_lazy_cong refl)
  by (simp add: nth_append_left)

lemma
  state_k_bound :
    \<open>AE state in run_steps_lazy xs initial_state. state_k state \<le> length xs\<close>
    (is ?thesis_0) and
  state_chi_bound :
    \<open>AE state in run_steps_lazy xs initial_state. state_chi state \<subseteq> set xs\<close>
    (is ?thesis_1)
proof -
  let ?P = \<open>\<lambda> index state.
    state_k state \<le> index \<and> state_chi state \<subseteq> set xs\<close>

  have \<open>\<turnstile>pmf
    \<lbrakk>(\<lambda> state.
      (index, i) \<in> set (List.enumerate 0 [0 ..< length xs]) \<and>
      ?P index state)\<rbrakk>
    step_lazy xs i
    \<lbrakk>?P (Suc index)\<rbrakk>\<close> for index i
    by (auto simp add:
      step_lazy_def step_1_lazy_def' step_2_lazy_def'
      AE_measure_pmf_iff in_set_enumerate_eq)

  then have \<open>AE state in run_steps_lazy xs initial_state. ?P (length xs) state\<close>
    apply (intro Utils_PMF_Hoare.loop[
      where offset = 0 and xs = \<open>[0 ..< length xs]\<close>, simplified])
    by (auto simp add: initial_state_def)

  then show ?thesis_0 ?thesis_1 by simp_all
qed

end

end