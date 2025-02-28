section \<open>Main CVM correctness theorem\<close>

text
  \<open>Top level correctness theorems for the CVM algorithm.

  These are established by the following results:
  \begin{itemize}
    \item \texttt{cvm\_estimate\_is\_nat}
    says that the resulting estimate returned by \texttt{cvm}
    (ie the CVM algorithm) is a natural number (on top of being a real number).

    \item \texttt{cvm\_correct\_of\_empty\_or\_threshold}
    formalises the observation that \texttt{cvm} always gives the correct, exact
    estimate if the input list \texttt{xs} is nonempty, and that the
    threshold is not so large that it exceeds \texttt{card (set xs)}.

    \item \texttt{prob\_cvm\_incorrect\_le}
    is the main correctness theorem as in Theorem 2 of \cite{cvm_2023}.

    Note that:
    \begin{itemize}
      \item As with the earlier results we formalised, the version we have
      here is more general than the one in \cite{cvm_2023}, because we prove it
      for a range of values for the threshold subject to some constraints
      (which include the one used there).

      Later, in \texttt{CVM\_Correctness\_Instance}, we obtain
      \texttt{prob\_cvm\_incorrect\_le\_delta}, a stronger version of
      (the correctness part of) Theorem 2 of \cite{cvm_2023}.

      \item This result uses the above one to provide an API that allows one
      to ignore trivial cases like the input list being empty, and the
      threshold being too large, when instantiating it with a threshold and
      proving the required constraints.
    \end{itemize}
  \end{itemize}\<close>

theory CVM_Correctness

imports
  CVM_Error_Bounds

begin

context cvm_algo
begin

theorem cvm_estimate_is_nat :
  \<open>\<turnstile>spmf \<lbrace>\<lblot>True\<rblot>\<rbrace> cvm \<lbrace>flip (\<in>) \<nat>\<rbrace>\<close>
  unfolding cvm_def compute_estimate_def
  apply (simp add: field_simps)
  by (metis (mono_tags) Num.of_nat_simps(5) of_nat_in_Nats of_nat_numeral of_nat_power)

theorem cvm_correct_of_empty_or_threshold :
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
    by (intro pmf_hoare_foldM_indexed) simp_all

  then show ?thesis
    unfolding cvm_def compute_estimate_def initial_state_def foldM_spmf_eq_foldM_pmf_case 
    by (auto simp add: AE_measure_pmf_iff map_pmf_eq_return_pmf_iff)
qed

end

context cvm_error_bounds
begin

definition \<open>prob_fail_bound \<equiv> length xs * f ^ threshold\<close>

abbreviation \<open>card_xs \<equiv> card (set xs)\<close>

abbreviation \<open>two_l_threshold \<equiv> 2 ^ l * threshold\<close>

lemmas prob_bounds_defs =
  prob_fail_bound_def
  prob_k_gt_l_bound_def
  prob_k_le_l_and_est_out_of_range_bound_def

theorem prob_cvm_incorrect_le :
  assumes
    \<open>0 < \<epsilon>\<close> \<open>0 \<le> \<delta>\<close>
    \<open>\<lbrakk>xs \<noteq> []; threshold \<le> card_xs\<rbrakk> \<Longrightarrow>
      \<epsilon> \<le> 1 \<and>
      2 \<le> r \<and> r \<le> threshold \<and>
      \<epsilon>\<^sup>2 * threshold \<ge> 6 * r \<and>
      r * card_xs \<le> two_l_threshold \<and> two_l_threshold \<le> 2 * r * card_xs \<and>
      prob_fail_bound + prob_k_gt_l_bound + prob_k_le_l_and_est_out_of_range_bound
      \<le> \<delta>\<close>
  shows
    \<open>\<P>(estimate in cvm xs.
      estimate |> is_None_or_pred
        (\<lambda> estimate. estimate >[\<epsilon>] card (set xs)))
    \<le> \<delta>\<close>
    (is \<open>?L \<le> ?R\<close>)
proof (cases \<open>xs = [] \<or> threshold > card (set xs)\<close>)
  case True
  with assms have \<open>?L = 0\<close>
    by (simp add: cvm_correct_of_empty_or_threshold algebra_split_simps)

  with assms show ?thesis by (simp add: prob_bounds_defs)
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

  also from
    assms \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close>
    prob_eager_algo_k_gt_l_le prob_eager_algo_k_le_l_and_est_out_of_range_le
  have \<open>\<dots> \<le> ?R\<close> unfolding prob_bounds_defs by fastforce

  finally show ?thesis .
qed

end

end