theory Utils_Real

imports
  HOL.MacLaurin
  (* "HOL-Analysis.Harmonic_Numbers" *)

begin

lemma exp_minus_one_le_half :
  \<open>exp (- (1 :: real)) < 1 / 2\<close>
  by (metis exp_diff exp_ge_add_one_self exp_gt_zero exp_zero less_divide_eq_numeral1(1) linorder_neqE_linordered_idom ln_2_less_1 ln_exp mult.commute one_add_one pos_less_divide_eq verit_comp_simplify1(1) verit_comp_simplify1(3) verit_minus_simplify(3) verit_minus_simplify(4))

end