theory CVM_Correctness

imports
  CVM_Error_Bounds

begin

context cvm_algo
begin

lemma cvm_estimate_is_nat :
  \<open>\<turnstile>spmf \<lbrace>\<lblot>True\<rblot>\<rbrace> cvm \<lbrace>flip (\<in>) \<nat>\<rbrace>\<close>
  unfolding compute_estimate_def
  apply (simp add: field_simps)
  by (metis (mono_tags) Num.of_nat_simps(5) of_nat_in_Nats of_nat_numeral of_nat_power)

lemma estimate_distinct_correct_of_empty_or_threshold :
  assumes \<open>xs = [] \<or> threshold > card (set xs)\<close>
  shows \<open>cvm xs = return_spmf (card <| set xs)\<close>
proof -
  let ?step = \<open>case_option fail_spmf <<< step\<close>
  let ?P = \<open>\<lambda> index.
    (=) (Some \<lparr>state_k = 0, state_chi = set (take index xs)\<rparr>)\<close>

  from assms have \<open>\<turnstile>pmf
    \<lbrakk>(\<lambda> state. (index, x) \<in> set (List.enumerate 0 xs) \<and> ?P index state)\<rbrakk>
    ?step x
    \<lbrakk>?P (Suc index)\<rbrakk>\<close> for index x
    unfolding compute_estimate_def step_def step_1_def' step_2_def' step_3_def
    apply (simp add: AE_measure_pmf_iff in_set_enumerate_eq)
    by (metis List.finite_set Un_insert_right append.right_neutral bot_nat_0.extremum_strict card_mono less_irrefl_nat list.set(2) list.size(3) order.strict_trans1 set_append
      set_take_subset take_Suc_conv_app_nth)

  then have \<open>\<turnstile>pmf \<lbrakk>?P 0\<rbrakk> foldM_pmf ?step xs \<lbrakk>?P (length xs)\<rbrakk>\<close>
    apply (intro Utils_PMF_FoldM_Hoare.loop[where offset = 0, simplified])
      by auto

  then show ?thesis
    unfolding cvm_def compute_estimate_def initial_state_def foldM_spmf_eq_foldM_pmf_case 
    by (auto simp add: AE_measure_pmf_iff map_pmf_eq_return_pmf_iff)
qed

end

context cvm_error_bounds 
begin

definition \<open>prob_fail_bound \<equiv> length xs * f ^ threshold\<close>

lemmas prob_bounds_defs =
  prob_fail_bound_def
  prob_k_gt_l_bound_def
  prob_k_le_l_and_est_out_of_range_bound_def

end

locale cvm_correctness = cvm_error_bounds +
  assumes assms :
    \<open>0 < \<epsilon>\<close>
    \<open>\<lbrakk>xs \<noteq> []; threshold \<le> (card <| set xs)\<rbrakk> \<Longrightarrow>
      \<epsilon> \<le> 1 \<and>
      r \<in> {2 .. threshold} \<and>
      \<epsilon>\<^sup>2 * threshold \<ge> 6 * r \<and>
      2 ^ l * threshold \<in> {r * (card <| set xs) .. 2 * r * (card <| set xs)}\<close>
begin

theorem prob_cvm_incorrect_le :
  \<open>\<P>(estimate in cvm xs.
      estimate |> is_None_or_pred
        (\<lambda> estimate. estimate >[\<epsilon>] card (set xs)))
  \<le> prob_fail_bound +
    prob_k_gt_l_bound +
    prob_k_le_l_and_est_out_of_range_bound\<close>
  (is \<open>?L \<le> _\<close>)
proof (cases \<open>xs = [] \<or> threshold > card (set xs)\<close>)
  case True
  with assms have \<open>?L = 0\<close>
    by (simp add:
      estimate_distinct_correct_of_empty_or_threshold algebra_split_simps)

  then show ?thesis by (simp add: prob_bounds_defs)
next
  case False
  then have \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close> by simp_all

  with assms interpret cvm_error_bounds_assms threshold r l \<epsilon> xs
    by unfold_locales fastforce

  let ?run_eager_algo =
    \<open>run_with_bernoulli_matrix <|
      run_reader <<< flip run_steps_eager initial_state\<close>

  from prob_run_steps_is_None_or_pred_le
  have \<open>?L \<le>
    prob_fail_bound +
    \<P>(estimate in run_steps_no_fail xs initial_state.
      compute_estimate estimate >[\<epsilon>] card (set xs))\<close>
    unfolding prob_bounds_defs cvm_def
    apply simp unfolding comp_apply .

  also from run_steps_no_fail_eq_run_steps_eager_bernoulli_matrix[where xs = xs]
  have \<open>\<dots> \<le> (
    prob_fail_bound +
    \<P>(state in ?run_eager_algo. state_k state > l) +
    \<P>(state in ?run_eager_algo. 
      state_k state \<le> l \<and> compute_estimate state >[\<epsilon>] card (set xs)))\<close>
    by (fastforce intro: pmf_add)

  finally show ?thesis
    using
      prob_eager_algo_k_gt_l_le assms
      prob_eager_algo_k_le_l_and_est_out_of_range_le
      \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close>
    by (force simp add: prob_bounds_defs)
qed

end

thm
  cvm_correctness.prob_cvm_incorrect_le[simplified cvm_correctness_def, simplified]
  cvm_error_bounds.prob_bounds_defs

end