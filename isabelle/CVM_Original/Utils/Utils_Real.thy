theory Utils_Real

imports
  HOL.Real

begin

lemma Ball_iff_prod_of_bool_eq_1 :
  assumes \<open>finite A\<close>
  shows \<open>Ball A P \<longleftrightarrow> (\<Prod> x \<in> A. of_bool (P x)) = (1 :: real)\<close>
  using assms
  apply (induction rule: finite_induct)
  by simp_all

end