theory Utils_Real

imports
  HOL.MacLaurin

begin

lemma exp_minus_one_le_half :
  \<open>exp (- (1 :: real)) < 1 / 2\<close>
  by (metis exp_less_cancel_iff exp_ln exp_minus' ln_2_less_1 verit_negate_coefficient(2) zero_less_numeral)

end