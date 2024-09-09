theory Utils_Approx_Algo

imports
  "HOL-Probability.Probability_Mass_Function"

begin

abbreviation eps_del_approxs (\<open>_ \<approx> \<langle> _ , _ \<rangle> _\<close>) where
  \<open>f \<approx>\<langle>\<epsilon>, \<delta>\<rangle> x \<equiv> \<P>(\<omega> in measure_pmf f. \<bar>\<omega> - x\<bar> > \<epsilon> * x) \<le> \<delta>\<close>

locale approx_algo =
  fixes \<epsilon> \<delta> :: real
begin

lemma approx_correct_of_correct :
  fixes
    f :: \<open>real pmf\<close> and
    x :: real
  assumes
    \<open>\<epsilon> \<ge> 0\<close> and
    \<open>\<delta> \<ge> 0\<close> and
    \<open>x \<ge> 0\<close> and
    \<open>f = return_pmf x\<close>
  shows \<open>f \<approx>\<langle>\<epsilon>, \<delta>\<rangle> x\<close>

  using assms by (simp add: mult_less_0_iff)

lemma eps_del_approx_iff [simp] :
 fixes
    f :: \<open>real pmf\<close>
  shows
    \<open>(\<forall> x \<epsilon> \<delta>. (f \<approx>\<langle>\<epsilon>, \<delta>\<rangle> x))
      \<longleftrightarrow> (\<forall> x \<epsilon> \<delta>. \<delta> \<le> 1 \<longrightarrow> (f \<approx>\<langle>\<epsilon>, \<delta>\<rangle> x))\<close>

  by (meson dual_order.refl linorder_not_le order_less_trans)

lemma relax_eps_del_approx :
  fixes \<epsilon>' \<delta>' x :: real
  assumes
    \<open>f \<approx>\<langle>\<epsilon>, \<delta>\<rangle> x\<close> and
    \<open>\<epsilon> > 0\<close> and
    \<open>\<delta> > 0\<close> and
    \<open>\<epsilon>' \<ge> \<epsilon>\<close> and
    \<open>\<delta>' \<ge> \<delta>\<close>
  shows \<open>f \<approx>\<langle>\<epsilon>', \<delta>'\<rangle> x\<close>

  using assms by (smt (verit, best) UNIV_I measure_pmf.finite_measure_mono mem_Collect_eq mult_pos_neg mult_right_mono sets_measure_pmf subsetI) 

end

end