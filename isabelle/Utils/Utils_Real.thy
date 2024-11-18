theory Utils_Real

imports
  HOL.MacLaurin

begin

(* lemma of_nat_less_0_iff [simp]: "(of_nat k :: real) < 0 \<Longrightarrow> k < 0"
  by linarith

lemma of_nat_le_0_iff [simp]: "(of_nat k :: real) \<le> 0 \<Longrightarrow> k \<le> 0"
  by linarith

lemma of_nat_0_le_iff [simp]: "0 \<le> (of_nat k :: real) \<Longrightarrow> 0 \<le> k"
  by linarith

lemma of_nat_less_1_iff [simp]: "(of_nat k :: real) < 1 \<Longrightarrow> k < 1"
  by linarith

lemma of_nat_le_1_iff [simp]: "(of_nat k :: real) \<le> 1 \<Longrightarrow> k \<le> 1"
  by linarith *)

lemma exp_minus_one_le_half :
  \<open>exp (- (1 :: real)) < 1 / 2\<close>
  by (metis exp_diff exp_ge_add_one_self exp_gt_zero exp_zero less_divide_eq_numeral1(1) linorder_neqE_linordered_idom ln_2_less_1 ln_exp mult.commute one_add_one pos_less_divide_eq verit_comp_simplify1(1) verit_comp_simplify1(3) verit_minus_simplify(3) verit_minus_simplify(4))

end