section \<open>Transforming CVM to CVM without failure\<close>

text
  \<open>This formalises the transformation from the original CVM algorithm (ie
  algorithm 1 in \cite{cvm_2023}) to a variation that does not fail (ie 
  algorithm 2).
  
  Here, \texttt{run\_steps} models algorithm 1, and
  \texttt{run\_steps\_no\_fail} models algorithm 2.
  
  The main result here is \texttt{prob\_run\_steps\_is\_None\_or\_pred\_le},
  which bounds the probability that \texttt{run\_steps} fails or gives the
  wrong estimate by its failure probability and that of
  \texttt{run\_steps\_no\_fail}.

  This is established by way of relational Hoare-like reasoning over the loops
  of both algorithms (modelled as monadic folds in \texttt{spmf}).\<close>

theory CVM_Algo_No_Fail

imports
  CVM_Algo
  Utils_SPMF_Rel_Hoare

begin

context cvm_algo
begin

abbreviation \<open>step_no_fail \<equiv> \<lambda> x state. step_1 x state \<bind> step_2\<close>
abbreviation \<open>step_no_fail_spmf \<equiv> \<lambda> x. spmf_of_pmf <<< step_no_fail x\<close>

abbreviation \<open>run_steps_no_fail \<equiv> foldM_pmf step_no_fail\<close>

abbreviation \<open>finite_chi \<equiv> finite <<< state_chi\<close>

end

context cvm_algo_assms
begin

text
  \<open>This loop invariant says that \texttt{state\_chi} always remains finite across
  the loop iterations of \texttt{run\_steps} and \texttt{run\_steps\_no\_fail}.
  This aids the simplifier in later lemmas.\<close>

lemma
  initial_state_finite :
    \<open>finite_chi initial_state\<close> (is ?thesis_0) and
  step_1_preserves_finiteness :
    \<open>\<turnstile>pmf \<lbrakk>finite_chi\<rbrakk> step_1 x \<lbrakk>finite_chi\<rbrakk>\<close> (is \<open>PROP ?thesis_1\<close>) and
  step_2_preserves_finiteness :
    \<open>\<turnstile>pmf \<lbrakk>finite_chi\<rbrakk> step_2 \<lbrakk>finite_chi\<rbrakk>\<close> (is \<open>PROP ?thesis_2\<close>) and
  step_preserves_finiteness :
    \<open>\<turnstile>spmf \<lbrace>finite_chi\<rbrace> step x \<lbrace>finite_chi\<rbrace>\<close> (is \<open>PROP ?thesis_3\<close>)
proof -
  show ?thesis_0 by (simp add: initial_state_def)
  show \<open>PROP ?thesis_1\<close>
    unfolding step_1_def' by (simp add: AE_measure_pmf_iff remove_def)
  moreover show \<open>\<turnstile>pmf \<lbrakk>finite_chi\<rbrakk> step_2 \<lbrakk>finite_chi\<rbrakk>\<close>
    unfolding step_2_def' by (simp add: AE_measure_pmf_iff)
  ultimately show \<open>PROP ?thesis_3\<close>
    unfolding step_def step_3_def
    by (fastforce
      simp flip: bind_spmf_of_pmf
      simp add: AE_measure_pmf_iff
      split: if_splits)
qed

text
  \<open>This uses the previous invariant to establish that \texttt{step\_2} has finite
  support after \texttt{step\_1}, so that we can split up an expectation over
  \texttt{step\_1 >>= step\_2} into iterated integrals.\<close>

lemma
  step_1_finite_support :
    \<open>\<And> state. finite <| set_pmf <| step_1 x state\<close> (is \<open>PROP ?thesis_0\<close>) and
  step_2_finite_support :
    \<open>\<And> state. finite_chi state \<Longrightarrow> finite <| set_pmf <| step_2 state\<close>
    (is \<open>PROP ?thesis_1\<close>) and
  step_2_finite_support_after_step_1 :
    \<open>\<turnstile>pmf \<lbrakk>finite_chi\<rbrakk> step_1 x \<lbrakk>(\<lambda> state. finite (set_pmf <| step_2 state))\<rbrakk>\<close>
    (is \<open>PROP ?thesis_2\<close>)
proof -
  show \<open>PROP ?thesis_0\<close> unfolding step_1_def' by simp
  moreover show \<open>\<And> state. finite_chi state \<Longrightarrow> finite <| set_pmf <| step_2 state\<close>
    unfolding step_2_def' by (simp add: set_prod_pmf finite_PiE)
  moreover note step_1_preserves_finiteness
  ultimately show \<open>PROP ?thesis_2\<close> by (fastforce simp add: AE_measure_pmf_iff)
qed

text \<open>Bounding the probability of failure of algorithm 2, \texttt{run\_steps}\<close>

lemma prob_fail_step_le :
  assumes \<open>finite_chi state\<close>
  shows \<open>prob_fail (step x state) \<le> f ^ threshold\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  have \<open>?L =
    measure_pmf.expectation (step_1 x state \<bind> step_2) (prob_fail <<< step_3)\<close>
    unfolding step_def pmf_bind_spmf_None by simp

  text
    \<open>Use the previous invariant to split up the expectation into iterated
    integrals.\<close>
  also from assms step_2_finite_support_after_step_1 step_1_finite_support
  have \<open>\<dots> =
    measure_pmf.expectation (step_1 x state)
      (\<lambda> state.
        measure_pmf.expectation (step_2 state)
        (prob_fail <<< step_3))\<close>
    (is \<open>_ = measure_pmf.expectation _ ?prob_fail_step_3_after_step_2\<close>)
    apply (subst integral_bind_pmf)
      by (fastforce simp add: AE_measure_pmf_iff)+

  also have \<open>\<dots> \<le> measure_pmf.expectation (step_1 x state) \<lblot>f ^ threshold\<rblot>\<close>
  proof -
    have
      \<open>?prob_fail_step_3_after_step_2 state \<le> f ^ threshold\<close> (is \<open>?L' \<le> ?R'\<close>)
      if \<open>finite_chi state\<close> for state :: \<open>'a state\<close>
    proof -
      let ?chi = \<open>state_chi state\<close>

      have \<open>?L' =
        of_bool (card ?chi = threshold) *
        measure_pmf.expectation (prod_pmf ?chi \<lblot>bernoulli_pmf f\<rblot>)
          (\<lambda> keep_in_chi.
            of_bool (card (Set.filter keep_in_chi ?chi) = card ?chi))\<close>
        by (auto intro!: integral_cong_AE simp add: step_2_def' step_3_def)

      also from that have \<open>\<dots> =
        of_bool (card ?chi = threshold) *
        measure_pmf.expectation (prod_pmf ?chi \<lblot>bernoulli_pmf f\<rblot>)
          (\<lambda> keep_in_chi. \<Prod> x \<in> ?chi. of_bool (keep_in_chi x))\<close>
        by (auto
          intro!: integral_cong_AE
          simp add: AE_measure_pmf_iff finset_card_filter_eq_iff_Ball)

      also from assms that have \<open>\<dots> \<le> ?R'\<close>
        apply (subst expectation_prod_Pi_pmf)
          by (simp_all add: integrable_measure_pmf_finite)

      finally show ?thesis .
    qed

    with assms step_1_preserves_finiteness show ?thesis
      apply (intro integral_mono_AE)
        by (fastforce simp add:
          integrable_measure_pmf_finite step_1_finite_support AE_measure_pmf_iff)+
  qed

  finally show ?thesis by simp
qed

lemma prob_fail_run_steps_le :
  \<open>prob_fail (run_steps xs initial_state) \<le> length xs * f ^ threshold\<close>
  by (metis prob_fail_foldM_spmf_le prob_fail_step_le step_preserves_finiteness initial_state_finite)

text
  \<open>\texttt{step\_le\_step\_no\_fail} says that if each loop iteration of
  algorithm 1 of \cite{cvm_2023} (ie \texttt{step}) terminates successfully
  (ie returns \texttt{Some}), then the corresponding iteration of algorithm 2
  (ie \texttt{step\_no\_fail}) also terminates successfully, and with the same
  result.

  \texttt{run\_steps\_le\_run\_steps\_no\_fail} extends the above result across
  the loop iterations to both algorithms
  (ie \texttt{run\_steps} and \texttt{run\_steps\_no\_fail}).

  These are formalised via $\sqsubseteq_{(=)}$, the flat CCPO ordering on
  \texttt{spmf}, with \texttt{foldM\_spmf\_ord\_spmf\_eq\_of\_ord\_spmf\_eq}
  using relational Hoare-like reasoning to extend the ordering across individual
  steps to the whole fold.
  
  This ordering in turn induces a corresponding ordering on their probability
  distributions, letting us conclude that the probability that algorithm 1
  terminates successfully and outputs the wrong estimate is $\le$ that of
  algorithm 2.\<close>

lemma step_le_step_no_fail :
  \<open>step x state \<sqsubseteq>\<^bsub>(=)\<^esub> spmf_of_pmf (step_no_fail x state)\<close>
  unfolding step_def step_3_def 
  apply (simp add: spmf_of_pmf_bind)
  by (smt (verit) bind_return_spmf ord_spmf_None ord_spmf_bind_reflI spmf.leq_refl)

lemma run_steps_le_run_steps_no_fail :
  \<open>run_steps xs state \<sqsubseteq>\<^bsub>(=)\<^esub> spmf_of_pmf (run_steps_no_fail xs state)\<close>
  unfolding foldM_spmf_of_pmf_eq[symmetric]
  by (blast intro: foldM_spmf_ord_spmf_eq_of_ord_spmf_eq step_le_step_no_fail)

text
  \<open>Main result bounding the probability that \texttt{run\_steps}
  (ie algorithm 1) fails or gives the wrong result.
  
  Note that this result is generic in the predicate P, which can be instantiated
  with the event that the resulting estimate is the wrong count.\<close>

theorem prob_run_steps_is_None_or_pred_le :
  \<open>\<P>(state in run_steps xs initial_state. state |> is_None_or_pred P)
  \<le> real (length xs) * f ^ threshold +
    \<P>(state in run_steps_no_fail xs initial_state. P state)\<close>
  (is \<open>?L is_None_or_pred \<le> ?R\<close>)
proof -
  have \<open>?L is_None_or_pred =
    prob_fail (run_steps xs initial_state) + ?L is_Some_and_pred\<close>
    by (metis measure_spmf_eq_measure_pmf_is_Some_and_pred prob_is_None_or_pred_eq_prob_fail_plus_prob)

  with
    prob_fail_run_steps_le
    prob_measure_spmf_le_of_ord_spmf[OF run_steps_le_run_steps_no_fail]
  show ?thesis
    by (smt (verit, del_insts) Collect_cong measure_spmf_eq_measure_pmf_is_Some_and_pred measure_spmf_spmf_of_pmf)
qed

end

end