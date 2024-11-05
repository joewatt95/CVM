theory Utils_Concentration_Inequalities

imports
  Concentration_Inequalities.Bennett_Inequality
  CVM.Utils_Function

begin

context prob_space
begin

context
  fixes t B :: real and X :: \<open>'b \<Rightarrow> 'a \<Rightarrow> real\<close> and I
  assumes I: "finite I"
  assumes ind: "indep_vars \<lblot>borel\<rblot> X I"
  assumes intsq: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. (X i x)\<^sup>2)"
  (* assumes bnd: "\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<ge> - B" *)
  assumes t: "t \<ge> 0"
  assumes B: "B > 0"
begin

abbreviation V :: real where "V \<equiv> (\<Sum>i \<in> I. expectation (\<lambda>x. (X i x)\<^sup>2))" 

abbreviation (input) \<open>go Y x \<equiv> (\<Sum> i \<in> I. Y i x - expectation (Y i))\<close>

abbreviation (input) "exp' \<equiv> exp (- (t\<^sup>2 / (2 * (V + t * B / 3))))"

lemma bernstein_inequality_le :
  assumes bnd: "\<And>i. i \<in> I \<Longrightarrow> AE x in M. X i x \<ge> - B"
  shows \<open>\<P>(x in M. go X x \<le> - t) \<le> exp'\<close>
proof -
  let ?Y = \<open>\<lambda> i. (-) (0) \<circ> X i\<close>

  note [simp] = comp_def

  have \<open>\<And>i. i \<in> I \<Longrightarrow> AE x in M. ?Y i x \<le> B\<close> using bnd by fastforce 

  moreover have \<open>(go X x \<le> -t) \<longleftrightarrow> (go ?Y x \<ge> t)\<close> for x
    by (simp, metis (mono_tags, lifting) minus_diff_eq more_arith_simps(1) sum.cong sum_negf)

  ultimately show ?thesis
    using
      bernstein_inequality[OF I, where X = ?Y, where t = t, where B = B]
      ind intsq bnd B t
      by (fastforce intro!: indep_vars_compose)
qed

end

end

end