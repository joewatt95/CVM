theory Distinct_Elems_Correctness

imports
  Utils_PMF_Bernoulli_Binomial
  Utils_PMF_Hoare
  Distinct_Elems_Error_Bounds_K_Exceeds_L
  Distinct_Elems_Error_Bounds_Est_Out_Of_Range

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

locale estimate_distinct_basic = with_threshold_r_l_\<epsilon>_xs
begin

definition
  \<open>prob_fprob_Nprob_faill (length xs) / 2 ^ threshold\<close>

lemmas prob_bounds_defs =
  prob_fail_bound_def
  prob_k_gt_l_bound_def
  prob_k_le_l_and_est_out_of_range_bound_def

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
      estimate |> is_None_or_pred
        (\<lambda> estimate. real estimate >[\<epsilon>] card (set xs)))
  \<le> probprobprob_fail
    prob_k_gt_l_bound +
    prob_k_le_l_and_est_out_of_range_bound\<close>
  (is \<open>?L \<le> _\<close>)
proof (cases \<open>xs = [] \<or> threshold > card (set xs)\<close>)
  case True
  with assms have \<open>?L = 0\<close>
    using zero_compare_simps(10)[of "\<bar>\<epsilon>\<bar>" "real (card (set xs))"]
    by (simp add: with_threshold.estimate_distinct_correct_of_empty_or_threshold)

  then show ?thesis by (simp add: prob_bounds_defs)
next
  case False
  then have \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close> by simp_all

  with assms interpret
    with_threshold_pos_r_l_\<epsilon>_xs threshold r l \<epsilon> xs
    by unfold_locales simp

  let ?run_eager_algo =
    \<open>run_with_bernoulli_matrix <|
      run_reader <<< eager_algorithm\<close>

  from prob_estimate_distinct_is_None_or_pred_le
  have \<open>?L \<le>
    prob_fail_bound +
    \<P>(estimate in estimate_distinct_no_fail xs.
      real estimate >[\<epsilon>] card (set xs))\<close>
    by (simp add: prob_bounds_defs)

  also have \<open>\<dots> \<le> (
    prob_fail_bound +
    \<P>(state in ?run_eager_algo. state_k state > l) +
    \<P>(state in ?run_eager_algo. 
      state_k state \<le> l \<and> real (compute_estimate state) >[\<epsilon>] card (set xs)))\<close>
    by (auto
      intro: pmf_add
      simp add:
        estimate_distinct_no_fail_eq_lazy_algo
        eager_lazy_conversion[of _ \<open>length xs\<close>])

  finally show ?thesis
    using
      prob_eager_algo_k_gt_l_le assms
      prob_eager_algo_k_le_l_and_est_out_of_range_le
      \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close>
    by (force simp add: prob_bounds_defs)
qed

end

text \<open>As before, but stated outside of our locales, for convenience and clarity.\<close>
theorem estimate_distinct_error_bound' :
  fixes
    \<epsilon> :: real and
    threshold l :: nat and
    xs :: \<open>'a list\<close>
  defines \<open>card_xs \<equiv> card (set xs)\<close>
  assumes
    \<open>0 < \<epsilon>\<close>
    \<open>\<lbrakk>xs \<noteq> []; threshold \<le> card_xs\<rbrakk> \<Longrightarrow>
      \<epsilon> \<le> 1 \<and>
      r \<in> {2 .. threshold} \<and>
      \<epsilon>\<^sup>2 * threshold \<ge> 6 * r \<and>
      2 ^ l * threshold \<in> {r * card_xs .. 2 * r * card_xs}\<close>
  defines
   \<open>prob_fprob_Nprob_fail
      real (length xs) / 2 ^ threshold\<close> and
   \<open>prob_k_gt_l_bound \<equiv>
      real (length xs) *
      exp (- 3 * real threshold * real ((r - 1)\<^sup>2) / real (5 * r + 2 * r\<^sup>2))\<close> and
   \<open>prob_k_le_l_and_est_out_of_range_bound \<equiv>
      4 * exp (- \<epsilon>\<^sup>2 * real threshold / (4 * real r * (1 + \<epsilon> / 3)))\<close>
  shows
    \<open>\<P>(estimate in with_threshold.estimate_distinct threshold xs.
      estimate |> is_None_or_pred
        (\<lambda> estimate. real estimate >[\<epsilon>] card (set xs)))
    \<le> probprobprob_fail
      prob_k_gt_l_bound +
      prob_k_le_l_and_est_out_of_range_bound\<close>
  using estimate_distinct.estimate_distinct_error_bound assms
  unfolding estimate_distinct_def estimate_distinct_basic.prob_bounds_defs
  by blast

end