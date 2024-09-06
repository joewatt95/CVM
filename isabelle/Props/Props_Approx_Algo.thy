theory Props_Approx_Algo

imports
  HOL.Power
  "HOL-Probability.Product_PMF"
  "HOL-Probability.Hoeffding"
  CVM.Utils_Function
  CVM.Utils_PMF
  CVM.Utils_Real

begin

abbreviation eps_del_approxs ("_ \<approx> \<langle> _ , _ \<rangle> _") where "
  f \<approx>\<langle>\<epsilon>, \<delta>\<rangle> x \<equiv> \<P>(\<omega> in measure_pmf f. \<bar>\<omega> - x\<bar> > \<epsilon> * x) \<le> \<delta>"

locale props_approx_algo =
  fixes \<epsilon> \<delta> :: real
begin

lemma approx_correct_of_correct :
  fixes
    f :: "real pmf" and
    x :: real
  assumes "
    \<epsilon> \<ge> 0" and "
    \<delta> \<ge> 0" and "
    x \<ge> 0" and "
    f = return_pmf x"
  shows "f \<approx>\<langle>\<epsilon>, \<delta>\<rangle> x"
  using assms by (simp add: mult_less_0_iff)

lemma eps_del_approx_iff [simp] :
 fixes
    f :: "real pmf"
  shows "
    (\<forall> x \<epsilon> \<delta>. (f \<approx>\<langle>\<epsilon>, \<delta>\<rangle> x))
    \<longleftrightarrow> (\<forall> x \<epsilon> \<delta>. \<delta> \<le> 1 \<longrightarrow> (f \<approx>\<langle>\<epsilon>, \<delta>\<rangle> x))"
  by (meson dual_order.refl linorder_not_le order_less_trans)

lemma relax_eps_del_approx :
  fixes \<epsilon>' \<delta>' x :: real
  assumes "
    f \<approx>\<langle>\<epsilon>, \<delta>\<rangle> x" and "
    \<epsilon> > 0" and "
    \<delta> > 0" and "
    \<epsilon>' \<ge> \<epsilon>" and "
    \<delta>' \<ge> \<delta>"
  shows "f \<approx>\<langle>\<epsilon>', \<delta>'\<rangle> x"
  using assms by (smt (verit, best) UNIV_I measure_pmf.finite_measure_mono mem_Collect_eq mult_pos_neg mult_right_mono sets_measure_pmf subsetI) 

end

end