theory CVM_Algo_Lazy_Eager

imports
  CVM_Algo_No_Fail
  Utils_Reader_Monad
  Utils_PMF_Lazify

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

    if card chi = threshold
    then do {
      keep_in_chi \<leftarrow> prod_pmf chi (\<lambda> _. bernoulli_pmf f);
      return_pmf \<lparr>state_k = k + 1, state_chi = Set.filter keep_in_chi chi\<rparr> }
    else return_pmf state }\<close>

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
  by (fastforce
    intro: bind_pmf_cong foldM_cong step_lazy_cong
    simp add: foldM_pmf_snoc upt_Suc_append nth_append_left)

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

context
  fixes xs :: \<open>'a list\<close> and i :: nat
begin

definition step_1_eager ::
  \<open>'a state \<Rightarrow> (coin_matrix, 'a state) reader_monad\<close> where
  \<open>step_1_eager \<equiv> \<lambda> state. do {
    let k = state_k state; let chi = state_chi state;
    insert_x_into_chi \<leftarrow> map_rd (\<lambda> \<phi>. (\<forall> k' < k. \<phi> (k', i))) get_rd;

    let chi = (chi |>
      if insert_x_into_chi
      then insert (xs ! i)
      else Set.remove (xs ! i));

    return_rd (state \<lparr>state_chi := chi\<rparr>) }\<close>

definition step_2_eager ::
  \<open>'a state \<Rightarrow> (coin_matrix, 'a state) reader_monad\<close> where
  \<open>step_2_eager \<equiv> \<lambda> state. do {
    let k = state_k state; let chi = state_chi state;

    if real (card chi) = threshold
    then do {
      keep_in_chi \<leftarrow> map_rd
        (\<lambda> \<phi>. \<lambda> x \<in> chi. \<phi> (k, last_index_up_to i xs x)) get_rd;
      return_rd \<lparr>state_k = k+1, state_chi = Set.filter keep_in_chi chi\<rparr> }
    else return_rd state }\<close>

definition step_eager ::
  \<open>'a state \<Rightarrow> (nat \<times> nat \<Rightarrow> bool, 'a state) reader_monad\<close> where
  \<open>step_eager \<equiv> \<lambda> state. step_1_eager state \<bind> step_2_eager\<close>

lemmas step_1_eager_def' = step_1_eager_def[
  simplified map_rd_def[symmetric] map_comp_rd Let_def if_distribR]

lemmas step_2_eager_def' = step_2_eager_def[
  simplified map_rd_def[symmetric] Let_def]

end

abbreviation
  \<open>run_steps_eager \<equiv> \<lambda> xs. foldM_rd (step_eager xs) [0 ..< length xs]\<close>

lemma step_eager_cong:
  assumes \<open>i < length xs\<close> \<open>i < length ys\<close> \<open>take (Suc i) xs = take (Suc i) ys\<close>
  shows
    \<open>step_1_eager xs i = step_1_eager ys i\<close> (is ?thesis_0)
    \<open>step_2_eager xs i = step_2_eager ys i\<close> (is ?thesis_1)
    \<open>step_eager xs i = step_eager ys i\<close> (is ?thesis_2)
proof -
  from assms have \<open>xs ! i = ys ! i\<close> by (simp add: take_Suc_conv_app_nth)

  moreover from assms have
    \<open>last_index_up_to i xs = last_index_up_to i ys\<close>
    unfolding last_index_up_to_def by simp
 
  ultimately show ?thesis_0 ?thesis_1 ?thesis_2
    unfolding step_eager_def step_1_eager_def' step_2_eager_def'
    by (simp_all cong: if_cong)
qed

lemma run_steps_eager_snoc :
  \<open>run_steps_eager (xs @ [x]) state =
    run_steps_eager xs state \<bind> step_eager (xs @ [x]) (length xs)\<close>
  by (fastforce
    intro: bind_cong_rd foldM_cong step_eager_cong
    simp add: foldM_rd_snoc upt_Suc_append nth_append_left)

abbreviation \<open>coin_pmf \<equiv> bernoulli_pmf f\<close>

context
  fixes n :: nat
begin

interpretation lazify "{..< n} \<times> {..< n}" "undefined" "\<lambda> _. coin_pmf"
  by unfold_locales simp

lemma depends_on_step1:
  fixes xs x \<phi> state
  defines "l \<equiv> length xs"
  shows "depends_on (step_1_eager (xs @ [x]) l state) ({..<state_k state}\<times>{l})"
proof -
  let ?S = "{..<state_k state} \<times> {l}"

  have "c1 (k',l) = c2 (k',l)"
    if "restrict c1 ?S = restrict c2 ?S" "k' < state_k state"
    for c1 c2 :: "nat \<times> nat \<Rightarrow> bool" and k'
  proof -
    have "c1 (k',l) = restrict c1 ?S (k',l)" using that(2) by simp
    also have "... = restrict c2 ?S (k',l)" using that(1) by simp
    also have "... = c2 (k',l)" using that(2) by simp
    finally show ?thesis by simp
  qed

  thus ?thesis
    unfolding step_1_eager_def' Let_def
    by (intro depends_on_bind depends_on_return depends_on_map) auto
qed

lemma depends_on_step2:
  fixes xs x \<sigma>
  defines
    "k' \<equiv> state_k \<sigma> + of_bool (card (state_chi \<sigma>) \<ge> threshold)" and
    "l \<equiv> length xs"
  shows "depends_on
    (step_2_eager (xs @ [x]) l \<sigma>)
    ({state_k \<sigma> ..< k'} \<times> {.. Suc l})"
proof (cases "card (state_chi \<sigma>) = threshold")
  case False
  then show ?thesis unfolding step_2_eager_def' by (simp add:Let_def depends_on_return)
next
  define keep_in_chi :: "(coin_matrix, 'a \<Rightarrow> bool) reader_monad" where
    "keep_in_chi \<equiv> map_rd
      (\<lambda> \<phi>. \<lambda> i \<in> state_chi \<sigma>. \<phi> (state_k \<sigma>, last_index_up_to l (xs @ [x]) i))
      get_rd"

  case True
  then have b: "k' = Suc (state_k \<sigma>)" unfolding k'_def by simp

  from True depends_on_return
  have a:"step_2_eager (xs @ [x]) l \<sigma> =
    map_rd
      (\<lambda>c. \<lparr>state_k = (Suc <| state_k \<sigma>), state_chi = Set.filter c (state_chi \<sigma>)\<rparr>)
      keep_in_chi"
    unfolding step_2_eager_def' by (simp flip: keep_in_chi_def)

  have "depends_on keep_in_chi ({state_k \<sigma>} \<times> {.. Suc l})"
    unfolding keep_in_chi_def
    apply (intro depends_on_map ext)
    apply simp
    by (smt (verit, del_insts) atMost_iff last_index_up_to_le insertI1 mem_Sigma_iff restrict_apply')

  thus ?thesis
    unfolding a b map_rd_def
    apply (intro depends_on_bind depends_on_return)
    by simp
qed

end

end

end