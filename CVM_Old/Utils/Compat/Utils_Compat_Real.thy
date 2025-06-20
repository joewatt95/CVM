theory Utils_Compat_Real

imports
  HOL.Transcendental

begin

lemma powr_ge_zero' :
  \<open>0 \<le> x powr y\<close> for x y :: real
  by (simp add: powr_def)

lemma log_divide_pos' :
  \<open>x > 0 \<Longrightarrow> y > 0 \<Longrightarrow> log a (x / y) = log a x - log a y\<close>
  using log_divide by auto

(* lemma real_le_1_iff [simp]: "real k \<le> 1 \<Longrightarrow> k \<le> 1"
  using of_nat_le_iff [of _ 1] by simp *)

end