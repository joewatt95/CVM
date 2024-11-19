theory Distinct_Elems_Correctness_Usage

imports
  CVM.Distinct_Elems_Correctness

begin

context
  fixes
    \<epsilon> \<delta> :: real and
    xs :: \<open>'a list\<close>
  assumes \<epsilon> : \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> and \<delta> : \<open>0 < \<delta>\<close> \<open>\<delta> \<le> 1\<close>
begin

definition \<open>threshold \<equiv> 12 * log 2 (8 * real (max 1 <| length xs) / \<delta>) / \<epsilon>\<^sup>2\<close>

definition
  \<open>l \<equiv> \<lfloor>log 2 <| 4 * card (set xs) / \<lceil>threshold\<rceil>\<rfloor>\<close>

context
  assumes
    \<open>xs \<noteq> []\<close>
    \<open>threshold \<le> card (set xs)\<close>
begin

lemma threshold_ge_2 :
  \<open>threshold \<ge> 2\<close> (is ?thesis_0)
proof -
  have \<open>log (2 :: real) 8 = 3\<close>
    by (metis Groups.mult_ac(1) log2_of_power_eq mult_2 numeral_Bit0 of_nat_numeral power3_eq_cube)

  with \<epsilon> \<delta> \<open>xs \<noteq> []\<close>
  show ?thesis_0
    apply (simp add: threshold_def log_divide log_mult nonempty_iff_length_ge_1 field_simps)
    by (smt (z3) Num.of_nat_simps(2) log_le_zero_cancel_iff numeral_nat(7) of_nat_mono power_le_one zero_le_log_cancel_iff)
qed

lemma \<epsilon>_threshold_ge_12 :
  \<open>\<epsilon>\<^sup>2 * threshold \<ge> 12\<close> (is ?thesis_0) 
  \<open>\<epsilon>\<^sup>2 * \<lceil>threshold\<rceil> \<ge> 12\<close> (is ?thesis_1) 
proof -
  from \<epsilon> \<delta> \<open>xs \<noteq> []\<close>
  show ?thesis_0
    by (simp add: threshold_def nonempty_iff_length_ge_1 field_simps)

  with \<epsilon> show ?thesis_1
    by (meson landau_omega.R_mult_left_mono le_of_int_ceiling order_trans_rules(23) zero_compare_simps(12))
qed

lemma l_pos : \<open>l > 0\<close>
  using \<open>threshold \<le> card (set xs)\<close> threshold_ge_2
  apply (simp add: l_def field_simps)
  by linarith

lemma two_l_threshold_bounds :
 \<open>2 * card (set xs) \<le> 2 ^ nat l * nat \<lceil>threshold\<rceil>\<close> (is \<open>?L0 \<le> ?R0\<close>)
 \<open>2 ^ nat l * nat \<lceil>threshold\<rceil> \<le> 4 * card (set xs)\<close> (is \<open>?L1 \<le> ?R1\<close>)
proof -
  from \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close> l_pos threshold_ge_2
  have \<open>log 2 ?L \<le> log 2 ?R\<close>
    apply (simp add: l_def log_mult log_divide field_simps split: if_splits)
    by (smt (z3) Num.of_nat_simps(2,4) log_pow_cancel nat_1_add_1 real_of_int_floor_add_one_ge real_sqrt_four real_sqrt_pow2)

  with \<open>threshold \<le> card (set xs)\<close> threshold_ge_2
  show \<open>?L0 \<le> ?R0\<close> by (simp add: nat_le_real_less)

  from \<open>threshold \<le> card (set xs)\<close> l_pos threshold_ge_2
  have \<open>2 ^ nat l \<le> 4 * card (set xs) / nat \<lceil>threshold\<rceil>\<close>
    apply (simp add: l_def)
    by (smt (verit) power_of_nat_log_le)

  with threshold_ge_2
  show \<open>?L1 \<le> ?R1\<close>
    apply (simp add: field_simps)
    apply (simp only: Multiseries_Expansion.intyness_simps)
    by (metis (no_types, lifting) Multiseries_Expansion.intyness_simps(2) mult_is_0 mult_le_mono2 nat_eq_iff2 of_int_of_nat_eq of_nat_le_iff zero_le_numeral)
qed

end

interpretation estimate_distinct_example :
  estimate_distinct \<open>nat \<lceil>threshold\<rceil>\<close> \<open>nat l\<close> 2 \<epsilon> xs
  apply unfold_locales
  using \<epsilon>(1) apply simp_all
  by (metis Distinct_Elems_Correctness_Usage.\<epsilon>_threshold_ge_12(2) Distinct_Elems_Correctness_Usage.threshold_ge_2 \<delta>(1) \<delta>(2) \<epsilon>(2) ceiling_mono ceiling_numeral nat_le_0 nat_mono nat_numeral_as_int of_nat_nat rel_simps(28) two_l_threshold_bounds(1) two_l_threshold_bounds(2) verit_la_generic)

lemma
  assumes \<open>0 < x\<close> \<open>0 < y\<close> \<open>y \<le> 1\<close>
  shows \<open>exp (- log 2 (8 * x / y)) \<le> y / (20 * x)\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  have \<open>?L = exp (log 2 <| y / (8 * x))\<close> using log_divide by fastforce

  also have \<open>\<dots> = (y / (8 * x)) powr log 2 (exp 1)\<close>
    sorry

  show ?thesis sorry
qed

lemma
  \<open>estimate_distinct_example.prob_fail_bound \<le> \<delta> / 8\<close>
proof -
  thm estimate_distinct_example.prob_fail_bound_def

  show ?thesis
   sorry

qed

end


end