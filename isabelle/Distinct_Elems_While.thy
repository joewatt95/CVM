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

lemma compute_estimate_eq_compute_estimate_truncate :
  \<open>compute_estimate =
    (state.truncate :: 'a state_with_bad_flag \<Rightarrow> 'a state)
      >>> compute_estimate\<close>
  by (auto simp add: compute_estimate_def state.defs)

lemma foldM_pmf_truncate_eq_map_truncate_foldM_pmf :
  assumes
    \<open>\<And> x state. f x (state.truncate state) = map_pmf state.truncate (g x state)\<close>
  shows
    \<open>foldM_pmf f xs (state.truncate state) =
      map_pmf state.truncate (foldM_pmf g xs state)\<close>
  using assms unfolding state.defs
  apply (induction xs arbitrary: state)
  by (auto intro: bind_pmf_cong simp add: map_bind_pmf bind_map_pmf)

lemma foldM_spmf_truncate_eq_map_truncate_foldM_spmf :
  assumes
    \<open>\<And> x state. f x (state.truncate state) = map_spmf state.truncate (g x state)\<close>
  shows
    \<open>foldM_spmf f xs (state.truncate state) =
      map_spmf state.truncate (foldM_spmf g xs state)\<close>
  using assms unfolding state.defs
  apply (induction xs arbitrary: state)
  by (auto intro: bind_spmf_cong simp add: map_spmf_bind_spmf bind_map_spmf)

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
  \<open>step_while_with_bad_flag \<equiv> \<lambda> x state. do {
    let state = state.truncate state;

    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ (state_k state);

    let chi = (state
      |> state_chi
      |> if insert_x_into_chi
        then insert x
        else Set.remove x);

    let state = state\<lparr>state_chi := chi\<rparr>;

    if card chi < threshold
    then return_spmf (state.extend state \<lparr>state_bad_flag = False\<rparr>)
    else do {
      state \<leftarrow> body state;
      if card (state_chi state) < threshold
      then return_spmf (state.extend state \<lparr>state_bad_flag = False\<rparr>)
      else (state
        |> loop_spmf.while cond body_spmf
        |> map_spmf (flip state.extend \<lparr>state_bad_flag = True\<rparr>)) }}\<close>

definition estimate_distinct_while_with_bad_flag :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_distinct_while_with_bad_flag \<equiv>
    run_steps_then_estimate_spmf
      step_while_with_bad_flag initial_state_with_bad_flag\<close>

end

context with_threshold_pos
begin

definition step_with_bad_flag ::
  \<open>'a \<Rightarrow> 'a state_with_bad_flag \<Rightarrow> 'a state_with_bad_flag pmf\<close> where
  \<open>step_with_bad_flag \<equiv> \<lambda> x.
    step_no_fail x >>> map_pmf (state_bad_flag_update \<lblot>False\<rblot>)\<close>

definition step_fail_on_bad_event ::
  \<open>'a \<Rightarrow> 'a state_with_bad_flag \<Rightarrow> 'a state_with_bad_flag spmf\<close> where
  \<open>step_fail_on_bad_event \<equiv> \<lambda> x.
    f_fail_on_bad_event cond (spmf_of_pmf <<< step_with_bad_flag x)\<close>

definition estimate_distinct_with_bad_flag :: \<open>'a list \<Rightarrow> nat pmf\<close> where
  \<open>estimate_distinct_with_bad_flag \<equiv>
    run_steps_then_estimate_pmf
      step_with_bad_flag initial_state_with_bad_flag\<close>

lemma step_while_eq_with_bad_flag :
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

lemma estimate_distinct_while_eq_with_bad_flag :
  \<open>estimate_distinct_while xs = estimate_distinct_while_with_bad_flag xs\<close>
  apply (simp add:
    estimate_distinct_while_def estimate_distinct_while_with_bad_flag_def state.defs
    run_steps_then_estimate_def initial_state_def initial_state_with_bad_flag_def)
  using
    compute_estimate_eq_compute_estimate_truncate
    foldM_spmf_truncate_eq_map_truncate_foldM_spmf[
      of step_while, OF step_while_eq_with_bad_flag,
      simplified state.defs]
   by (smt (verit) bind_pmf_cong map_option_cong map_pmf_def map_return_pmf option.map(2) spmf.map_comp state.select_convs(1,2))

lemma step_no_fail_eq_with_bad_flag :
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

lemma estimate_distinct_no_fail_eq_with_bad_flag :
  \<open>estimate_distinct_no_fail xs = estimate_distinct_with_bad_flag xs\<close>
  apply (simp add:
    estimate_distinct_no_fail_def estimate_distinct_with_bad_flag_def state.defs
    run_steps_then_estimate_def initial_state_def initial_state_with_bad_flag_def)
  using
    compute_estimate_eq_compute_estimate_truncate
    foldM_pmf_truncate_eq_map_truncate_foldM_pmf[
      of step_no_fail, OF step_no_fail_eq_with_bad_flag,
      simplified state.defs]
  by (metis (no_types, lifting) ext map_pmf_comp state.simps(1,2))

lemma step_eq_fail_on_bad_event :
  \<open>step x (state.truncate state) = (
    state
      |> step_fail_on_bad_event x 
      |> map_spmf state.truncate)\<close>
  by (auto
    intro!: bind_spmf_cong
    simp flip: bind_spmf_of_pmf map_spmf_of_pmf
    simp add:
      step_fail_on_bad_event_def cond_def f_fail_on_bad_event_def step_with_bad_flag_def
      step_def step_no_fail_def Let_def state.defs spmf_of_pmf_bind fail_spmf_def
      well_formed_state_def map_spmf_bind_spmf bind_map_spmf comp_def)

lemma estimate_distinct_eq_fail_on_bad_event :
  \<open>estimate_distinct xs =
    run_steps_then_estimate_spmf
      step_fail_on_bad_event initial_state_with_bad_flag xs\<close>
  apply (simp add:
    estimate_distinct_def estimate_distinct_with_bad_flag_def state.defs
    run_steps_then_estimate_def initial_state_def initial_state_with_bad_flag_def)
  using
    compute_estimate_eq_compute_estimate_truncate
    foldM_spmf_truncate_eq_map_truncate_foldM_spmf[
      of step, OF step_eq_fail_on_bad_event,
      simplified state.defs]
  by (smt (verit) bind_pmf_cong map_option_cong map_pmf_def map_return_pmf option.simps(9) spmf.map_comp state.select_convs(1,2))

lemma truncate_preserves_well_formed_state_iff :
  \<open>\<turnstile>spmf \<lbrace>well_formed_state\<rbrace> map_spmf state.truncate <<< f \<lbrace>well_formed_state\<rbrace> \<longleftrightarrow>
    \<turnstile>spmf \<lbrace>well_formed_state\<rbrace> f \<lbrace>well_formed_state\<rbrace>\<close> (is ?thesis_0)
  \<open>\<turnstile>spmf \<lbrace>well_formed_state\<rbrace> g <<< state.truncate \<lbrace>well_formed_state\<rbrace> \<longleftrightarrow>
    \<turnstile>spmf \<lbrace>well_formed_state\<rbrace> g \<lbrace>well_formed_state\<rbrace>\<close> (is ?thesis_1)
proof - 
  show ?thesis_0
    by (fastforce
      simp add: Utils_SPMF_Hoare.hoare_triple_def well_formed_state_def state.defs)
  
  show ?thesis_1
    apply (simp add:
      Utils_SPMF_Hoare.hoare_triple_def well_formed_state_def state.defs)
    by (metis (mono_tags, lifting) state.cases state.select_convs(1,2))
qed

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
  (is \<open>?L estimate_distinct_no_fail_spmf estimate_distinct_while \<le> ?R\<close>)
proof -
  note [simp] =
    space_measure_spmf well_formed_state_def Let_def Set.remove_def

  have
    \<open>?L estimate_distinct_no_fail_spmf estimate_distinct_while =
      ?L
        (spmf_of_pmf <<< estimate_distinct_with_bad_flag)
        estimate_distinct_while_with_bad_flag\<close>
    by (simp add: estimate_distinct_no_fail_eq_with_bad_flag estimate_distinct_while_eq_with_bad_flag)

  also have \<open>\<dots> \<le> prob_fail (foldM_spmf step_fail_on_bad_event xs initial_state_with_bad_flag)\<close>
    apply (simp
      add:
        estimate_distinct_with_bad_flag_def estimate_distinct_while_with_bad_flag_def
        estimate_distinct_def run_steps_then_estimate_def step_fail_on_bad_event_def 
        compute_estimate_def measure_map_spmf
      flip: map_spmf_of_pmf foldM_spmf_of_pmf_eq)

    apply (intro prob_foldM_spmf_diff_le_prob_fail_foldM_fail_on_bad_event[
      where invariant = \<open>finite <<< state_chi\<close>,
      where invariant' = well_formed_state,
      where bad_event' = \<open>state_bad_flag\<close>,
      simplified])

      subgoal
        apply (simp
          add: step_with_bad_flag_def map_spmf_conv_bind_spmf
          flip: map_spmf_of_pmf bind_spmf_of_pmf)
        apply (intro Utils_SPMF_Hoare.seq'[where Q = \<open>finite <<< state_chi\<close>])
        by (auto
          intro!:
            Utils_SPMF_Hoare.if_then_else
            Utils_SPMF_Hoare.seq'[where Q = \<open>\<lblot>True\<rblot>\<close>]
            Utils_SPMF_Hoare.postcond_true
          simp flip: bind_spmf_of_pmf
          simp add: step_no_fail_def spmf_of_pmf_bind if_distrib)

      subgoal
        by (metis (no_types, lifting) ext step_while_eq_with_bad_flag step_while_preserves_well_formedness truncate_preserves_well_formed_state_iff(1,2))

      subgoal
        apply (simp flip: space_measure_spmf weight_spmf_def lossless_spmf_def)
        using step_while_eq_with_bad_flag[unfolded state.defs]
        by (metis (lifting) lossless_map_spmf lossless_step_while state.simps(2) well_formed_state_def)

      subgoal
        apply (simp
          flip: map_spmf_of_pmf bind_spmf_of_pmf
          add:
            step_with_bad_flag_def step_while_with_bad_flag_def step_no_fail_def
            map_spmf_conv_bind_spmf spmf_of_pmf_bind if_distrib)
        unfolding state.defs Let_def if_distribR
        apply (intro Utils_SPMF_Relational.seq'[where S = \<open>(=)\<close>])
        apply (simp add: Utils_SPMF_Relational.relational_hoare_triple_def)
        apply (intro Utils_SPMF_Relational.if_then_else)
        apply (auto
          intro!: rel_spmf_bindI[where R = \<open>(=)\<close>]
          simp flip: map_spmf_of_pmf bind_spmf_of_pmf
          simp add:
            cond_def body_def spmf_of_pmf_bind
            Utils_SPMF_Relational.relational_hoare_triple_def
            spmf_rel_map rel_spmf_return_spmf1)
        apply simp
        apply (intro lossless_step_while_loop[simplified cond_def body_def Let_def spmf_of_pmf_bind, simplified])
        apply simp
        apply (metis card_insert_if card_mono finite_insert linorder_neqE_nat member_filter not_less_eq state.select_convs(2) subsetI)
        by (meson card_Diff1_le order.strict_trans1)

      using threshold_pos
      by (simp_all add: initial_state_with_bad_flag_def initial_state_def state.defs)

  also have \<open>\<dots> = ?R\<close>
    by (simp add: estimate_distinct_eq_fail_on_bad_event prob_fail_map_spmf_eq run_steps_then_estimate_def)

  finally show ?thesis .
qed

end

end