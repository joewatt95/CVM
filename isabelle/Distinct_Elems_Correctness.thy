theory Distinct_Elems_Correctness

imports
  CVM.Utils_PMF_Bernoulli_Binomial
  CVM.Utils_PMF_Hoare
  CVM.Error_Bounds_K_Exceeds_L
  CVM.Error_Bounds_Est_Out_Of_Range

begin

context with_threshold
begin

lemma estimate_distinct_correct_of_empty_or_threshold :
  assumes \<open>xs = [] \<or> threshold > card (set xs)\<close>
  shows \<open>estimate_distinct xs = return_spmf (card <| set xs)\<close>
proof -
  let ?step = \<open>\<lambda> x. case_option fail_spmf (step x)\<close>
  let ?P = \<open>\<lambda> index.
    (=) (Some \<lparr>state_k = 0, state_chi = set (take index xs)\<rparr>)\<close>

  have \<open>\<turnstile>pmf
    \<lbrakk>(\<lambda> state. (index, x) \<in> set (List.enumerate 0 xs) \<and> ?P index state)\<rbrakk>
    ?step x
    \<lbrakk>?P (Suc index)\<rbrakk>\<close> for index x
    using
      assms card_set_take_le_card_set[of "Suc index" xs]
      insert_nth_set_take_eq_set_take_Suc[of index xs]
    by (auto simp add:
      Utils_PMF_Hoare.hoare_triple_def step_def in_set_enumerate_eq)

  then have \<open>\<turnstile>pmf
    \<lbrakk>?P 0\<rbrakk>
    map_spmf compute_estimate <<< foldM_pmf ?step xs
    \<lbrakk>flip (=) (Some <| card <| set xs)\<rbrakk>\<close>
    using Utils_PMF_Hoare.loop[where offset = 0]
    by (force
      intro: Utils_PMF_Hoare.seq
      simp add: map_pmf_def compute_estimate_def)

  then show ?thesis
    using map_pmf_eq_return_pmf_iff
    by (force simp add:
      estimate_distinct_def run_steps_then_estimate_def initial_state_def
      foldM_spmf_eq_foldM_pmf_case Utils_PMF_Hoare.hoare_triple_def image_def)
qed

end

locale estimate_distinct_basic =
  fixes
    threshold l r :: nat and
    xs :: \<open>'a list\<close> and
    \<epsilon> :: real
begin

definition
  \<open>prob_fail_bound \<equiv> real (length xs) / 2 ^ threshold\<close>

definition
  \<open>prob_eager_algo_k_gt_l_le_bound \<equiv>
    real (length xs) *
    exp (-3 * real threshold * (r - 1)\<^sup>2 / (5 * r + 2 * r\<^sup>2))\<close>

definition
  \<open>prob_eager_algo_k_le_l_and_estimate_out_of_range_bound \<equiv>
    4 * exp (-\<epsilon>\<^sup>2 * threshold / (4 * real r * (1 + 1 * \<epsilon> / 3)))\<close>

lemmas prob_bounds_defs =
  prob_fail_bound_def
  prob_eager_algo_k_gt_l_le_bound_def
  prob_eager_algo_k_le_l_and_estimate_out_of_range_bound_def

end

locale estimate_distinct = estimate_distinct_basic +
  assumes assms :
    \<open>0 < \<epsilon>\<close>
    \<open>\<lbrakk>xs \<noteq> []; threshold \<le> (card <| set xs)\<rbrakk> \<Longrightarrow>
      \<epsilon> \<le> 1 \<and>
      r \<in> {2 .. threshold} \<and>
      \<epsilon>\<^sup>2 * threshold \<ge> 6 * r \<and>
      2 ^ l * threshold \<in> {r * (card <| set xs) .. 2 * r * (card <| set xs)}\<close>
begin

theorem estimate_distinct_error_bound :
  \<open>\<P>(estimate in with_threshold.estimate_distinct threshold xs.
      estimate |> fails_or_satisfies
        (\<lambda> estimate. real estimate >[\<epsilon>] card (set xs)))
  \<le> prob_fail_bound +
    prob_eager_algo_k_gt_l_le_bound +
    prob_eager_algo_k_le_l_and_estimate_out_of_range_bound\<close>
  (is \<open>?L \<le> _\<close>)
proof (cases \<open>xs = [] \<or> threshold > card (set xs)\<close>)
  case True
  then have \<open>?L = 0\<close>
    using assms zero_compare_simps(10)[of "\<bar>\<epsilon>\<bar>" "real (card (set xs))"]
    by (simp add: with_threshold.estimate_distinct_correct_of_empty_or_threshold)

  then show ?thesis by (simp add: prob_bounds_defs)
next
  case False
  then have
    \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close> by simp_all

  with assms interpret with_params :
    with_threshold_pos_r_l_xs threshold r l xs
    apply unfold_locales by simp

  let ?run_eager_algo =
    \<open>with_params.run_with_bernoulli_matrix <|
      run_reader <<< with_params.eager_algorithm\<close>

  have \<open>?L \<le>
    prob_fail_bound +
    \<P>(estimate in with_params.estimate_distinct_no_fail xs.
      real estimate >[\<epsilon>] card (set xs))\<close>
    using with_params.prob_estimate_distinct_fails_or_satisfies_le
    by (simp add: prob_bounds_defs)

  also have \<open>\<dots> \<le> (
    prob_fail_bound +
    \<P>(state in ?run_eager_algo. state_k state > l) +
    \<P>(state in ?run_eager_algo. 
      state_k state \<le> l \<and> real (compute_estimate state) >[\<epsilon>] card (set xs)))\<close>
    by (auto
      intro: pmf_add
      simp add:
        with_params.estimate_distinct_no_fail_eq_lazy_algo
        with_params.eager_lazy_conversion[of _ \<open>length xs\<close>])

  finally show ?thesis
    using
      with_params.prob_eager_algo_k_gt_l_le assms
      with_params.prob_eager_algo_k_le_l_and_est_out_of_range_le
      \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close>
    by (force simp add: prob_bounds_defs)
qed

end

end