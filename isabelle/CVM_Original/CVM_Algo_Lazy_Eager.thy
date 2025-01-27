theory CVM_Algo_Lazy_Eager

imports
  CVM_Algo_No_Fail
  Utils_Reader_Monad

begin

hide_const (open) Misc_CryptHOL.coin_pmf

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

abbreviation \<open>well_formed_state \<equiv> \<lambda> xs state.
  state_k state \<le> length xs \<and> state_chi state \<subseteq> set xs\<close>

lemma run_steps_lazy_preserves_well_formedness :
  \<open>AE state in run_steps_lazy xs initial_state. well_formed_state xs state\<close>
  (is \<open>AE state in _. ?P (length xs) state\<close>)
proof -
  have \<open>\<turnstile>pmf
    \<lbrakk>(\<lambda> state.
      (index, i) \<in> set (List.enumerate 0 [0 ..< length xs]) \<and>
      ?P index state)\<rbrakk>
    step_lazy xs i
    \<lbrakk>?P (Suc index)\<rbrakk>\<close> for index i
    by (auto simp add:
      step_lazy_def step_1_lazy_def' step_2_lazy_def'
      AE_measure_pmf_iff in_set_enumerate_eq)

  then show ?thesis
    apply (intro Utils_PMF_Hoare.loop[
      where offset = 0 and xs = \<open>[0 ..< length xs]\<close>, simplified])
    by (auto simp add: initial_state_def)
qed

theorem run_steps_no_fail_eq_lazy :
  \<open>run_steps_no_fail xs initial_state = run_steps_lazy xs initial_state\<close>
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)

  moreover have
    \<open>step_lazy (xs @ [x]) (length xs) state = step_no_fail x state\<close> for state
    unfolding
      step_lazy_def step_1_lazy_def' step_2_lazy_def' step_1_def' step_2_def'
      bind_map_pmf
    apply (intro bind_pmf_cong refl)
    by simp

  ultimately show ?case
    unfolding run_steps_lazy_snoc foldM_pmf_snoc by presburger
qed

type_synonym coin_matrix = \<open>nat \<times> nat \<Rightarrow> bool\<close>

definition step_1_eager ::
  \<open>'a list \<Rightarrow> nat \<Rightarrow> 'a state \<Rightarrow> (coin_matrix, 'a state) reader_monad\<close> where
  \<open>step_1_eager \<equiv> \<lambda> xs i state. do {
    let k = state_k state; let chi = state_chi state;
    insert_x_into_chi \<leftarrow> map_rd (\<lambda> \<phi>. (\<forall> k' < k. \<phi> (k', i))) get_rd;

    let chi = (chi |>
      if insert_x_into_chi
      then insert (xs ! i)
      else Set.remove (xs ! i));

    return_rd (state \<lparr>state_chi := chi\<rparr>) }\<close>

(* definition step_2_eager :: "'a list \<Rightarrow> nat \<Rightarrow> 'a state \<Rightarrow> (coin_matrix, 'a state) reader_monad"
  where "step_2_eager xs i state = do {
      let k = state_k state;
      let chi = state_chi state;
      if real (card chi) < threshold then
        return_rd (state\<lparr>state_chi := chi\<rparr>)
      else do {
        keep_in_chi \<leftarrow> map_rd (\<lambda>\<phi>. \<lambda>x \<in> chi. \<phi> (k, find_last_before i x xs)) get_rd;
        let chi = Set.filter keep_in_chi chi;
        return_rd \<lparr>state_k = k+1, state_chi = chi\<rparr>
      }
    }"

definition eager_step :: "'a list \<Rightarrow> nat \<Rightarrow> 'a state \<Rightarrow> (coin_matrix, 'a state) reader_monad"
  where
  "eager_step xs i state = step_1_eager xs i state \<bind> step_2_eager xs i"
*)

lemmas step_1_eager_def' = step_1_eager_def[
  simplified map_rd_def[symmetric] Let_def]

end

end