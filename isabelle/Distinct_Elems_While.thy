theory Distinct_Elems_While

imports
  CVM.Distinct_Elems_Algo
  CVM.Algo_Transforms_No_Fail
  CVM.Utils_PMF_Bernoulli_Binomial

begin

record 'a state_with_bad_flag = \<open>'a state\<close> +
  state_bad_flag :: bool

definition initial_state_with_bad_flag :: \<open>'a state_with_bad_flag\<close> where
  \<open>initial_state_with_bad_flag \<equiv>
    state.extend initial_state \<lparr>state_bad_flag = False\<rparr>\<close>

context with_threshold
begin

definition cond :: \<open>('a, 'b) state_scheme \<Rightarrow> bool\<close> where
  \<open>cond \<equiv> \<lambda> state. card (state_chi state) \<ge> threshold\<close>

definition body :: \<open>('a, 'b) state_scheme \<Rightarrow> ('a, 'b) state_scheme pmf\<close> where
 \<open>body \<equiv> \<lambda> state. do {
  let chi = state_chi state;

  keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
    prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

  let chi = Set.filter keep_in_chi chi;
  let k = state_k state + 1;

  return_pmf (state\<lparr>state_k := k, state_chi := chi\<rparr>)}\<close>

abbreviation \<open>body_spmf \<equiv> spmf_of_pmf <<< body\<close>

definition step_while ::
  \<open>'a \<Rightarrow> ('a, 'b) state_scheme \<Rightarrow> ('a, 'b) state_scheme spmf\<close> where
  \<open>step_while x state \<equiv> do {
    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ (state_k state);

    let chi = (state
      |> state_chi
      |> if insert_x_into_chi
        then insert x
        else Set.remove x);

    loop_spmf.while cond body_spmf (state\<lparr>state_chi := chi\<rparr>) }\<close>

definition estimate_distinct_while :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_distinct_while \<equiv>
    run_steps_then_estimate_spmf step_while initial_state\<close>

(* Note that this unrolls the while loop _twice_ in order to match the structure
of `step` and `step_no_fail`. *)
definition step_while_with_bad_flag ::
  \<open>'a \<Rightarrow> 'a state_with_bad_flag \<Rightarrow> 'a state_with_bad_flag spmf\<close> where
  \<open>step_while_with_bad_flag x state \<equiv> do {
    let bad_flag = state_bad_flag state;
    let state = state.truncate state;

    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ (state_k state);

    let chi = (state
      |> state_chi
      |> if insert_x_into_chi
        then insert x
        else Set.remove x);

    let state = state\<lparr>state_chi := chi\<rparr>;

    if card chi < threshold
    then return_spmf (state.extend state \<lparr>state_bad_flag = bad_flag\<rparr>)
    else do {
      state \<leftarrow> body state;
      if card (state_chi state) < threshold
      then return_spmf (state.extend state \<lparr>state_bad_flag = bad_flag\<rparr>)
      else (state
        |> loop_spmf.while cond body_spmf
        |> map_spmf (flip state.extend \<lparr>state_bad_flag = True\<rparr>)) }}\<close>

definition estimate_distinct_while_with_bad_flag :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_distinct_while_with_bad_flag \<equiv>
    run_steps_then_estimate_spmf
      step_while_with_bad_flag initial_state_with_bad_flag\<close>

(* definition step_with_bad_flag ::
  \<open>'a \<Rightarrow> 'a state_with_bad_flag \<Rightarrow> 'a state_with_bad_flag pmf\<close> where
  \<open>step_with_bad_flag x state \<equiv> do {
    let bad_flag = state_bad_flag state;
    let state = state.truncate state;

    let k = state_k state;
    let chi = state_chi state;

    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ k;

    let chi = (chi |>
      if insert_x_into_chi
      then insert x
      else Set.remove x);

    let state = state\<lparr>state_chi := chi\<rparr>;

    if card chi < threshold
    then return_pmf (state.extend state \<lparr>state_bad_flag = bad_flag\<rparr>)
    else (\<lblot>bernoulli_pmf <| 1 / 2\<rblot>
      |> prod_pmf chi
      |> map_pmf (\<lambda> keep_in_chi. (
        \<lparr>state_k = k + 1, state_chi = Set.filter keep_in_chi chi\<rparr>
          |> flip state.extend
            \<lparr>state_bad_flag = bad_flag \<or> card chi \<ge> threshold\<rparr>))) }\<close> *)

end

context with_threshold_pos
begin

definition step_with_bad_flag ::
  \<open>'a \<Rightarrow> 'a state_with_bad_flag \<Rightarrow> 'a state_with_bad_flag pmf\<close> where
  \<open>step_with_bad_flag x \<equiv>
    step_no_fail x
      >>> map_pmf (\<lambda> state. state\<lparr>state_bad_flag := False\<rparr>)\<close>

definition estimate_distinct_with_bad_flag :: \<open>'a list \<Rightarrow> nat pmf\<close> where
  \<open>estimate_distinct_with_bad_flag \<equiv>
    run_steps_then_estimate_pmf
      step_with_bad_flag initial_state_with_bad_flag\<close>

lemma step_while_eq_step_while_with_bad_flag :
  \<open>step_while x (state.truncate state) = (
    state
      |> step_while_with_bad_flag x
      |> map_spmf state.truncate)\<close>
proof -
  have [intro!] : \<open>p = map_spmf f p\<close> if \<open>\<And> x. f x = x\<close> for f and p :: \<open>'c spmf\<close>
    using that by (simp add: map_spmf_idI)

  show ?thesis
    by (fastforce
      intro!: bind_spmf_cong
      simp flip: bind_spmf_of_pmf
      simp add:
        state.defs comp_def Let_def well_formed_state_def
        step_while_def step_while_with_bad_flag_def with_threshold.cond_def
        loop_spmf.while_simps map_spmf_bind_spmf bind_map_spmf spmf.map_comp)
qed

(* lemma
  \<open>estimate_distinct_while x (state.truncate state) = (
    state
      |> estimate_distinct_while_with_bad_flag x
      |> map_spmf state.truncate)\<close>
  sorry *)

lemma step_no_fail_eq_step_with_bad_flag :
  \<open>step_no_fail x (state.truncate state) = (
    state
      |> step_with_bad_flag x
      |> map_pmf state.truncate)\<close>
  by (fastforce
    intro: bind_pmf_cong
    simp flip: map_pmf_def
    simp add:
      state.defs Let_def if_distrib map_bind_pmf bind_map_pmf map_pmf_comp
      step_no_fail_def step_with_bad_flag_def)

lemma
  \<open>estimate_distinct_no_fail xs = estimate_distinct_with_bad_flag xs\<close>
  apply (simp
    add:
      estimate_distinct_no_fail_def estimate_distinct_with_bad_flag_def state.defs
      run_steps_then_estimate_def initial_state_def initial_state_with_bad_flag_def)
  unfolding compute_estimate_def
  sorry

lemma
  \<open>step x (state.truncate state) = (
    state
      |> f_fail_on_bad_event (\<lambda> state. card (state_chi state) \<ge> threshold)
        (spmf_of_pmf <<< step_with_bad_flag x)
      |> map_spmf state.truncate)\<close>
  by (auto
    intro!: bind_spmf_cong
    simp flip: bind_spmf_of_pmf map_spmf_of_pmf
    simp add:
      f_fail_on_bad_event_def step_with_bad_flag_def step_def step_no_fail_def
      Let_def state.defs spmf_of_pmf_bind fail_spmf_def well_formed_state_def 
      map_spmf_bind_spmf bind_map_spmf comp_def spmf.map_comp)

thm
  step_def
  step_while_with_bad_flag_def[
    simplified
      body_def Let_def spmf_of_pmf_bind spmf_of_pmf_return_pmf
      bind_spmf_of_pmf[symmetric] map_bind_spmf bind_map_spmf comp_def
      map_spmf_conv_bind_spmf[symmetric],
    simplified bind_spmf_of_pmf, simplified]

lemma step_while_preserves_well_formedness :
  \<open>\<turnstile>spmf \<lbrace>well_formed_state\<rbrace> step_while x \<lbrace>well_formed_state\<rbrace>\<close>
proof -
  let ?finite_chi = \<open>finite <<< state_chi\<close>

  let ?hoare_triple = \<open>\<lambda> f. \<turnstile>spmf
    \<lbrace>?finite_chi\<rbrace>
    (\<lambda> state. return_spmf (state\<lparr>state_chi := f (state_chi state)\<rparr>))
      >=> loop_spmf.while cond body_spmf
    \<lbrace>(\<lambda> state. \<not> cond state \<and> finite (state_chi state))\<rbrace>\<close>

  have \<open>?hoare_triple undefined id\<close>
    by (auto
      intro!: while Utils_SPMF_Hoare.seq'[where Q = \<open>\<lblot>True\<rblot>\<close>]
      simp add:
        cond_def body_def spmf_of_pmf_bind map_spmf_conv_bind_spmf Let_def
        card_mono subset_iff
      simp flip: bind_spmf_of_pmf map_spmf_of_pmf map_pmf_def)

  from this[simplified] have
    \<open>?hoare_triple undefined (insert x)\<close>
    \<open>?hoare_triple undefined (Set.remove x)\<close> for x :: 'a
    by (auto
      intro: Utils_SPMF_Hoare.seq'[where Q = ?finite_chi]
      simp add: Set.remove_def simp del: return_bind_spmf)

  then show ?thesis
    unfolding well_formed_state_def step_while_def bind_spmf_of_pmf[symmetric]
    apply (intro Utils_SPMF_Hoare.seq'[where Q = \<open>\<lblot>True\<rblot>\<close>])
    apply (simp_all add:
      Let_def cond_def not_le Utils_SPMF_Hoare.hoare_triple_def)
    by blast
qed

lemma lossless_step_while_loop :
  assumes \<open>finite (state_chi state)\<close> \<open>card (state_chi state) \<le> threshold\<close>
  shows \<open>lossless_spmf <| loop_spmf.while cond body_spmf state\<close>
proof -
  have
    \<open>{keep_in_chi. card (Set.filter keep_in_chi chi) \<ge> card chi} =
      chi \<rightarrow> {True}\<close>
    if \<open>finite chi\<close> for chi :: \<open>'a set\<close>
    using that
    apply (intro Set.set_eqI)
    apply (simp add: Pi_iff)
    by (metis card_mono card_seteq finite_filter member_filter subsetI)

  with threshold_pos have
    \<open>\<P>(state in body state. cond state) = 1 / 2 ^ threshold\<close>
    if
      \<open>cond state\<close> \<open>finite (state_chi state)\<close>
      \<open>card (state_chi state) \<le> threshold\<close>
    for state :: \<open>('a, 'b) state_scheme\<close>
    using that
    by (auto
      simp flip: map_pmf_def
      simp add:
        well_formed_state_def with_threshold.cond_def body_def card_ge_0_finite
        Let_def vimage_def measure_Pi_pmf_Pi measure_pmf_single field_simps)

  with assms threshold_pos show ?thesis
    by (auto
      intro!: termination_0_1_immediate_invar[
        where p = \<open>1 / 2 ^ threshold\<close>,
        where I = \<open>\<lambda> state.
          finite (state_chi state) \<and> card (state_chi state) \<le> threshold\<close>]
      simp add:
        body_def well_formed_state_def Let_def with_threshold.cond_def
        self_le_power pmf_map_pred_true_eq_prob pmf_False_conv_True
        card_mono subset_iff)
qed

lemma lossless_step_while :
  assumes \<open>state ok\<close>
  shows \<open>lossless_spmf <| step_while x state\<close>
  using assms lossless_step_while_loop well_formed_state_card_le_threshold[OF assms]
  apply (simp add: step_while_def well_formed_state_def Let_def Set.remove_def)
  by (smt (verit, ccfv_threshold) finite_Diff finite_insert less_le lossless_step_while_loop order.refl state.select_convs(2) state.surjective state.update_convs(2)
    well_formed_state_def)

lemma lossless_estimate_distinct_while [simp] :
  \<open>lossless_spmf <| estimate_distinct_while xs\<close>
  by (auto
    intro:
      lossless_foldM_spmf lossless_step_while initial_state_well_formed
      step_while_preserves_well_formedness
    simp add: estimate_distinct_while_def run_steps_then_estimate_def)

lemma
  \<open>\<bar>\<P>(state in measure_spmf <| estimate_distinct_no_fail_spmf xs. P state)
    - \<P>(state in measure_spmf <| estimate_distinct_while xs. P state)\<bar>
  \<le> prob_fail (estimate_distinct xs)\<close>
  (is \<open>?L \<le> ?R\<close>)
proof -
  note [simp] = space_measure_spmf well_formed_state_def Let_def Set.remove_def

  have \<open>?L \<le> prob_fail (foldM_spmf (f_fail_on_bad_event cond <<< step_no_fail_spmf) xs initial_state)\<close>
    apply (simp
      add:
        estimate_distinct_no_fail_def estimate_distinct_while_def
        estimate_distinct_def run_steps_then_estimate_def initial_state_def
        compute_estimate_def measure_map_spmf
      flip: map_spmf_of_pmf foldM_spmf_of_pmf_eq)

    apply (intro aux[
      where invariant = \<open>finite <<< state_chi\<close>,
      where invariant' = well_formed_state,
      simplified])
      subgoal using lossless_spmf_def by fastforce

      subgoal sorry
      subgoal sorry

      subgoal
        unfolding
          cond_def body_def step_no_fail_def step_while_def
          f_with_bad_flag_def map_spmf_conv_bind_spmf case_prod_beta
          map_pmf_def[symmetric] Let_def
        apply (simp
          flip: bind_spmf_of_pmf
          add: spmf_of_pmf_bind loop_spmf.while.simps)
        apply (rule Utils_SPMF_Relational.seq'[where S = \<open>(=)\<close>])
        apply (metis (mono_tags, lifting) Utils_SPMF_Relational.precond_strengthen Utils_SPMF_Relational.refl_eq(2))
        apply (simp add: if_distrib)

        (* TODO *)
        apply (rule Utils_SPMF_Relational.if_then_else')
          subgoal
            apply simp
            by (metis (lifting) ext Suc_lessI card.insert_remove card_Diff1_le less_not_refl order.strict_trans1)

          apply simp

          sorry

      using threshold_pos by simp_all

  also have \<open>\<dots> \<le> ?R\<close>
    sorry

  finally show ?thesis .
qed

(* lemma
  \<open>\<bar>\<P>(x in measure_spmf <| estimate_distinct_while xs. P x)
    - \<P>(x in measure_spmf <| estimate_distinct xs. P x)\<bar>
  \<le> length xs / 2 ^ threshold\<close>
  apply (induction xs)
  apply (simp_all add:
    estimate_distinct_while_def estimate_distinct_def run_steps_then_estimate_def
    step_def step_while_def initial_state_def
    measure_map_spmf vimage_def space_measure_spmf Let_def)
  unfolding Let_def Set.filter_def Set.remove_def if_distribR
  sorry *)

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