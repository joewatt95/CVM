theory Distinct_Elems_No_Fail_Unbiased

imports
  CVM.Distinct_Elems_Algo_Transforms_No_Fail

begin

abbreviation (input)
  \<open>aux \<equiv> \<lambda> x state. indicat_real (state_chi state) x * 2 ^ (state_k state)\<close>

locale state_finite_support =
  fixes state :: \<open>('a, 'b) state_scheme pmf\<close>
  assumes state_finite_support : \<open>finite <| set_pmf state\<close>

context
  fixes state :: \<open>('a, 'b) state_scheme pmf\<close>
  assumes state_finite_support : \<open>finite <| set_pmf state\<close>
begin

lemma step_1_preserves_finite_support :
  \<open>finite <| set_pmf <| state \<bind> step_1_no_fail x'\<close>
  using state_finite_support
  by (simp flip: map_pmf_def add: step_1_no_fail_def)

lemma step_1_preserves_expectation_eq_1 :
  assumes
    \<open>\<And> x. x \<in> S \<Longrightarrow> measure_pmf.expectation state (aux x) = 1\<close>
    \<open>x \<in> S \<or> x = x'\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step_1_no_fail x') (aux x) = 1\<close>
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

  with state_finite_support show ?thesis
    by (auto simp add: step_2_no_fail_def Let_def)
qed

lemma step_2_preserves_expectation_eq_1 :
  assumes
    \<open>\<And> x. x \<in> S \<Longrightarrow> measure_pmf.expectation state (aux x) = 1\<close>
    \<open>x \<in> S\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step_2_no_fail) (aux x) = 1\<close>
proof -
  from state_finite_support assms show ?thesis
    unfolding step_2_no_fail_def Let_def
    apply (subst pmf_expectation_bind)
    apply auto
    apply (subst set_prod_pmf)
    using not_less_iff_gr_or_eq threshold_pos apply fastforce
    apply (subst finite_UN)
    apply auto
    apply (metis card.infinite card_UNIV_bool finite_PiE semiring_norm(143) threshold_pos)

    apply (subst (asm) integral_measure_pmf)
    apply (auto
      simp flip: map_pmf_def
      simp add:
        if_distrib if_distribR sum.If_cases uminus_set_def fun_Compl_def not_less
        Set.filter_def algebra_simps)

    find_theorems "measure_pmf.expectation" "Pi_pmf"

    sorry
qed

end

end