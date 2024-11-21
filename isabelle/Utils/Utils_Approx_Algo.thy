theory Utils_Approx_Algo

imports
  "HOL-Probability.Probability_Mass_Function"

begin

abbreviation beyond_eps_range_of
  (\<open>_ >[ _ ] _\<close> [60, 60, 60] 60) where
  \<open>\<omega> >[\<epsilon>] x \<equiv> \<bar>\<omega> - x\<bar> > \<epsilon> * x\<close>

abbreviation eps_del_approxs
  (\<open>_ \<approx>[ _ , _ ] \<approx>>? _\<close> [60, 60, 60, 60] 60) where
  \<open>f \<approx>[\<epsilon>, \<delta>]\<approx>>? x \<equiv> \<P>(\<omega> in measure_pmf f. \<omega> >[\<epsilon>] x) \<le> \<delta>\<close>

context
  fixes \<epsilon> \<delta> :: real
begin

lemma approx_correct_of_correct :
  assumes
    \<open>\<epsilon> \<ge> 0\<close> \<open>\<delta> \<ge> 0\<close> \<open>x \<ge> 0\<close> 
    \<open>f = return_pmf x\<close>
  shows \<open>f \<approx>[\<epsilon>, \<delta>]\<approx>>? x\<close>
  using assms by (simp add: mult_less_0_iff)

lemma eps_del_approx_iff [simp] :
  \<open>(\<forall> x \<epsilon> \<delta>. f \<approx>[\<epsilon>, \<delta>]\<approx>>? x) \<longleftrightarrow> (\<forall> x \<epsilon> \<delta>. \<delta> \<le> 1 \<longrightarrow> f \<approx>[\<epsilon>, \<delta>]\<approx>>? x)\<close>
  by (meson dual_order.refl linorder_not_le order_less_trans)

lemma relax_eps_del_approx :
  assumes
    \<open>f \<approx>[\<epsilon>, \<delta>]\<approx>>? x\<close>
    \<open>\<epsilon> > 0\<close> \<open>\<delta> > 0\<close>
    \<open>\<epsilon>' \<ge> \<epsilon>\<close> \<open>\<delta>' \<ge> \<delta>\<close>
  shows \<open>f \<approx>[\<epsilon>', \<delta>']\<approx>>? x\<close>
  using assms
  by (smt (verit, best) UNIV_I measure_pmf.finite_measure_mono mem_Collect_eq mult_pos_neg mult_right_mono sets_measure_pmf subsetI)

end

end