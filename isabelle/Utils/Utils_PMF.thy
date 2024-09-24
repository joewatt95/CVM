theory Utils_PMF

imports
  "HOL-Probability.Probability_Mass_Function"
  CVM.Utils_Function

begin

abbreviation foldM_pmf ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b pmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b pmf\<close> where
  \<open>foldM_pmf \<equiv> foldM bind_pmf return_pmf\<close>

lemma bernoulli_pmf_one [simp] :
  \<open>bernoulli_pmf 1 = return_pmf True\<close>

  by (simp add: bernoulli_pmf.rep_eq pmf_eqI)

lemma binomial_pmf_one [simp] :
  \<open>binomial_pmf n 1 = return_pmf n\<close>

  by (metis set_pmf_binomial_1 set_pmf_subset_singleton subset_iff_psubset_eq) 

lemma map_pmf_times_one [simp] :
  fixes p :: \<open>nat pmf\<close>
  shows \<open>map_pmf ((*) <| Suc 0) p = p\<close>

  by (simp add: pmf.map_ident_strong) 

definition p::"bool pmf"
  where "p = bernoulli_pmf (1/2)"

definition q::"bool pmf"
  where "q = do {
    c1 \<leftarrow> bernoulli_pmf (1/2);
    c2 \<leftarrow> bernoulli_pmf (1/2);
    return_pmf (c1 = c2)
  }"

lemma rel_pmf_p_q:
  shows "rel_pmf (=) p q"
proof -
  let ?p = "p \<bind> (\<lambda> x. return_pmf x \<bind> return_pmf)"

  have "rel_pmf (=) ?p q"
    unfolding p_def q_def

    apply (rule rel_pmf_bindI[
      where ?R = "\<lambda> x y. x \<in> bernoulli_pmf (1/2) \<and> x = y"])

    apply (blast intro: rel_pmf_reflI)

    apply (rule rel_pmf_bindI[
      where ?R = "\<lambda> x y. x \<in> bernoulli_pmf (1/2) \<and> y \<in> bernoulli_pmf (1/2)"])

    apply (simp add: rel_pmf_return_pmf1)

    apply (subst rel_return_pmf)

    sorry 

  then show ?thesis by (simp add: bind_return_pmf')
qed

end