theory Utils_Concentration_Inequalities

imports
  Concentration_Inequalities.Bennett_Inequality
  CVM.Utils_Function

begin

context prob_space
begin

context
  fixes t B :: real and X :: \<open>'b \<Rightarrow> 'a \<Rightarrow> real\<close> and I
  assumes I : \<open>finite I\<close>
  assumes ind : \<open>indep_vars \<lblot>borel\<rblot> X I\<close>
  assumes intsq : \<open>\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. (X i x)\<^sup>2)\<close>
  assumes t : \<open>t \<ge> 0\<close>
  assumes B : \<open>B > 0\<close>
begin

abbreviation (input) \<open>sum_mean_deviation Y x \<equiv> (\<Sum> i \<in> I. Y i x - expectation (Y i))\<close>

abbreviation \<open>V \<equiv> (\<Sum>i \<in> I. expectation (\<lambda>x. (X i x)\<^sup>2))\<close>

abbreviation (input) "exp_bound \<equiv> exp (- (t\<^sup>2 / (2 * (V + t * B / 3))))"

lemma bernstein_inequality_le :
  assumes bnd: "\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<ge> - B"
  shows \<open>\<P>(x in M. sum_mean_deviation X x \<le> - t) \<le> exp_bound\<close>
proof -
  let ?Y = \<open>\<lambda> i. uminus \<circ> X i\<close>

  note [simp] = comp_def

  have \<open>\<And>i. i \<in> I \<Longrightarrow> AE x in M. ?Y i x \<le> B\<close> using bnd by fastforce 

  moreover have \<open>(sum_mean_deviation X x \<le> -t) \<longleftrightarrow> (sum_mean_deviation ?Y x \<ge> t)\<close> for x
    apply simp
    by (metis (mono_tags, lifting) minus_diff_eq more_arith_simps(1) sum.cong sum_negf)

  ultimately show ?thesis
    using
      bernstein_inequality[OF I, where X = ?Y, where t = t, where B = B]
      ind intsq bnd B t
    by (fastforce intro!: indep_vars_compose)
qed

lemma bernstein_inequality_abs_ge :
  assumes bnd: \<open>\<And>i. i \<in> I \<Longrightarrow> AE x in M. \<bar>X i x\<bar> \<le> B\<close>
  shows \<open>\<P>(x in M. \<bar>sum_mean_deviation X x\<bar> \<ge> t) \<le> 2 * exp_bound\<close> (is \<open>?L \<le> _\<close>)
proof -
  have
    \<open>{x \<in> space M. \<bar>sum_mean_deviation X x\<bar> \<ge> t} =
      {x \<in> space M. sum_mean_deviation X x \<le> -t} \<union> {x \<in> space M. sum_mean_deviation X x \<ge> t}\<close> by auto

  moreover have \<open>\<P>(x in M. sum_mean_deviation X x \<le> -t) \<le> exp_bound\<close>
    using bnd bernstein_inequality_le by fastforce

  moreover have \<open>\<P>(x in M. sum_mean_deviation X x \<ge> t) \<le> exp_bound\<close>
    using 
      bernstein_inequality[OF I, where X = X, where t = t, where B = B]
      ind intsq bnd B t
    by fastforce

  moreover have
    \<open>{x \<in> space M. sum_mean_deviation X x \<le> -t} \<in> events\<close>
    \<open>{x \<in> space M. sum_mean_deviation X x \<ge> t} \<in> events\<close>
    using ind[unfolded indep_vars_def] by (measurable, auto)+

  ultimately show ?thesis by (smt (verit) finite_measure_subadditive)
qed

end

end

end