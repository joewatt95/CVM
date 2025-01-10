theory Distinct_Elems_No_Fail_Unbiased

imports
  CVM.Distinct_Elems_Algo_Transforms_No_Fail

begin

abbreviation (input)
  \<open>aux \<equiv> \<lambda> f x state. indicat_real (f <| state_chi state) x * 2 ^ (state_k state)\<close>

context
  fixes state :: \<open>('a, 'b) state_scheme pmf\<close>
  assumes state_finite_support : \<open>finite <| set_pmf state\<close>
begin

lemma step_1_preserves_finite_support :
  \<open>finite <| set_pmf <| state \<bind> step_1_no_fail x'\<close>
  by (simp flip: map_pmf_def add: state_finite_support step_1_no_fail_def)

lemma step_1_preserves_expectation_eq_1 :
  assumes
    \<open>\<And> x. x \<in> S \<Longrightarrow> measure_pmf.expectation state (aux id x) = 1\<close>
    \<open>x \<in> S \<or> x = x'\<close>
  shows \<open>measure_pmf.expectation (state \<bind> step_1_no_fail x') (aux id x) = 1\<close>
proof -
  from assms have \<open>(x \<in> S \<and> x \<noteq> x') \<or> x = x'\<close> by blast

  (* x is an old element that has already been processed before, and is not
  equal to the new element x'. *)
  moreover from state_finite_support assms
  have ?thesis if \<open>x \<in> S\<close> \<open>x \<noteq> x'\<close>
    using that
    apply (simp add: step_1_no_fail_def flip: map_pmf_def)
    apply (subst integral_bind_pmf)
    by (auto simp add: indicator_def algebra_simps)

  ultimately show ?thesis 
    using state_finite_support assms
    by (auto
      simp flip: map_pmf_def
      simp add: step_1_no_fail_def pmf_expectation_bind sum_pmf_eq_1)
qed

end

context with_threshold_pos
begin

context
  fixes state :: \<open>('a, 'b) state_scheme pmf\<close>
  assumes state_finite_support : \<open>finite <| set_pmf state\<close>
begin

lemma step_2_preserves_finite_support :
  \<open>finite <| set_pmf <| state \<bind> step_2_no_fail\<close>
proof -
  from threshold_pos linorder_not_le have
    \<open>finite (set_pmf <| prod_pmf (state_chi state) \<lblot>bernoulli_pmf <| 1 / 2\<rblot>)\<close>
    if \<open>card (state_chi state) \<ge> threshold\<close> for state :: \<open>('a, 'b) state_scheme\<close>
    using that
    apply (subst set_prod_pmf)
    by (fastforce intro!: finite_PiE)+

  then show ?thesis
    by (auto simp add: state_finite_support step_2_no_fail_def Let_def)
qed

lemma step_2_preserves_expectation_eq_1 :
  assumes
    \<open>measure_pmf.expectation state (aux id x) = 1\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step_2_no_fail) (aux id x) = 1\<close>
    (is \<open>?L = _\<close>)
proof -
  have
    \<open>?L = (\<Sum> s \<in> set_pmf state.
      pmf state s * measure_pmf.expectation (step_2_no_fail s) (aux id x))\<close>
    proof -
      from assms threshold_pos not_le have \<open>\<turnstile>pmf
        \<lbrakk>\<lblot>True\<rblot>\<rbrakk> \<lblot>state\<rblot>
        \<lbrakk>(\<lambda> state.
          let chi = state_chi state
          in card chi \<ge> threshold \<longrightarrow>
            finite (
              \<Union> s \<in> set_pmf (prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>).
                {state\<lparr>
                  state_k := state_k state + 1,
                  state_chi := Set.filter s chi\<rparr>}))\<rbrakk>\<close>
        unfolding Let_def
        apply (intro Utils_PMF_Hoare.hoare_tripleI, safe)
        apply (subst set_prod_pmf)
        by (fastforce intro!: finite_UN_I finite_PiE)+

     with state_finite_support show ?thesis
      apply (subst pmf_expectation_bind)
      by (auto
        dest: Utils_PMF_Hoare.hoare_tripleE
        simp add: step_2_no_fail_def Let_def)
    qed

  also from state_finite_support have \<open>\<dots> = (
    \<Sum> s \<in> set_pmf state \<inter> {s. card (state_chi s) < threshold}.
      pmf state s * aux id x s) + (
    \<Sum> s \<in> set_pmf state \<inter> {s. card (state_chi s) \<ge> threshold \<and> x \<in> state_chi s}.
      pmf state s *
      measure_pmf.expectation
        (prod_pmf (state_chi s) \<lblot>bernoulli_pmf <| 1 / 2\<rblot>)
        (\<lambda> s'. 2 * aux (Set.filter s') x s))\<close>
    (is \<open>_ = sum ?f (?A (<)) + sum _ ?B\<close>)
    apply (simp
      flip: map_pmf_def
      add:
        step_2_no_fail_def if_distrib if_distribR Let_def
        sum.If_cases uminus_set_def fun_Compl_def not_less algebra_simps)
    apply (intro sum.mono_neutral_cong_right)
    by auto

  also have \<open>\<dots> =
    (\<Sum> s \<in> ?A (<). ?f s) + (\<Sum> s \<in> ?B.
      pmf state s * 2 ^ (state_k s + 1) *
      measure_pmf.expectation
        (bernoulli_pmf <| 1 / 2)
        (\<lambda> b. of_bool (x \<in> state_chi s \<and> b)))\<close>
    proof -
      from threshold_pos
      have \<open>finite chi\<close> if \<open>card chi \<ge> threshold\<close> for chi :: \<open>'a set\<close>
        using that leD by fastforce

      then show ?thesis
        unfolding add.left_cancel indicator_def
        apply (intro sum.cong, blast)
        apply (subst
          expectation_Pi_pmf_slice[where
            I = \<open>state_chi _\<close> and M = \<open>\<lblot>bernoulli_pmf <| 1 / 2\<rblot>\<close>, symmetric])
        by (auto simp add: integrable_measure_pmf_finite)
    qed

  also from state_finite_support have \<open>\<dots> =
    (\<Sum> s \<in> ?A (<). ?f s) + (\<Sum> s \<in> ?A (\<ge>). ?f s)\<close>
    by (auto intro: sum.mono_neutral_cong_left simp add: indicator_def)

  also from state_finite_support have \<open>\<dots> =
    measure_pmf.expectation state (aux id x)\<close>
    apply (subst sum.union_disjoint[symmetric])
    by (auto intro: sum.cong simp add: integral_measure_pmf)

  finally show ?thesis using assms by simp
qed

end

end