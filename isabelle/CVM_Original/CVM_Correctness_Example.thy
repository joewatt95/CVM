theory CVM_Correctness_Example

imports
  CVM_Correctness

begin

lemma exp_minus_log_le :
  assumes \<open>1 \<le> a\<close> \<open>1 \<le> b\<close> \<open>0 < c\<close> \<open>c \<le> 1\<close> 
  shows \<open>exp (- a * log 2 (8 * b / c)) \<le> c / (20 * b)\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  from assms
  have \<open>?L = exp (log 2 <| (c / (8 * b)) powr a)\<close>
    by (simp add: field_simps log_powr log_divide_pos)

  also from assms
  have \<open>\<dots> = ((c / (8 * b)) powr a) powr (1 / ln 2)\<close>
    by (simp add: powr_def)

  also from assms
  have \<open>\<dots> \<le> (c / (8 * b)) powr (1 / ln 2)\<close> (is \<open>_ \<le> ?exponentiate (c / _)\<close>)
    by (simp add: powr_le_one_le powr_mono2)

  also have \<open>\<dots> \<le> ?R\<close>
  proof -
    have \<open>?exponentiate 8 \<ge> 20\<close> by (approximation 13)

    with assms ln_2_less_1 have \<open>?exponentiate (8 * b) \<ge> 20 * b\<close>
      using mult_mono[of "20" "8 powr (Numeral1 / ln 2)" b "b powr (Numeral1 / ln 2)"] powr_mono[of Numeral1 "Numeral1 / ln 2" b]
      by (fastforce simp add: powr_mult)

    with assms ln_2_less_1 show ?thesis
      by (simp add: powr_divide frac_le powr_le_one_le)
  qed

  finally show ?thesis .
qed

context
  fixes
    \<epsilon> \<delta> :: real and
    xs :: \<open>'a list\<close>
begin

abbreviation (input) \<open>length_xs_1 \<equiv> max 1 (length xs)\<close>

definition \<open>threshold \<equiv> (12 / \<epsilon>\<^sup>2) * log 2 (8 * length_xs_1 / \<delta>)\<close>

definition \<open>l \<equiv> \<lfloor>log 2 <| 4 * card (set xs) / \<lceil>threshold\<rceil>\<rfloor>\<close>

context
  assumes
    \<epsilon> : \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> and
    \<delta> : \<open>0 < \<delta>\<close> \<open>\<delta> \<le> 1\<close>
begin

context
  assumes
    \<open>xs \<noteq> []\<close>
    \<open>threshold \<le> card (set xs)\<close>
begin

lemma threshold_ge_2 :
  \<open>\<lceil>threshold\<rceil> \<ge> 2\<close>
  using \<epsilon> \<delta> \<open>xs \<noteq> []\<close>
  apply (simp add: threshold_def)
  by (smt (verit, del_insts) Num.of_nat_simps(2) approximation_preproc_nat(8) log_divide_pos log_le_one_cancel_iff log_le_zero_cancel_iff numeral_nat(7) power2_nonneg_gt_1_iff)

lemma \<epsilon>_threshold_ge_12 :
  \<open>\<epsilon>\<^sup>2 * \<lceil>threshold\<rceil> \<ge> 12\<close>
  using \<epsilon> \<delta> \<open>xs \<noteq> []\<close>
  apply (simp add: threshold_def)
  by (smt (verit) Groups.mult_ac(2) approximation_preproc_nat(8) ceiling_divide_upper log_divide_pos log_le_zero_cancel_iff nat_le_real_less numeral_nat(7) one_le_log_cancel_iff one_of_nat_le_iff
    zero_less_power)

lemma two_l_threshold_bounds :
  defines [simp] : \<open>two_l_threshold \<equiv> 2 ^ nat l * nat \<lceil>threshold\<rceil>\<close>
  shows
    \<open>2 * card (set xs) \<le> two_l_threshold\<close> (is \<open>?lower \<le> _\<close>)
    \<open>two_l_threshold \<le> 4 * card (set xs)\<close> (is \<open>_ \<le> ?upper\<close>)
proof -
  from \<open>threshold \<le> card (set xs)\<close> threshold_ge_2
  have \<open>l > 0\<close>
    apply (simp add: l_def field_simps)
    by linarith

  with \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close> threshold_ge_2
  have \<open>log 2 ?lower \<le> log 2 two_l_threshold\<close>
    apply (simp add: l_def log_mult_pos log_divide_pos)
    by (smt (verit, best) Num.of_nat_simps(2) floor_eq_iff log2_of_power_eq numeral_Bit0_eq_double numerals(1) of_nat_numeral power2_eq_square)

  with \<open>threshold \<le> card (set xs)\<close> threshold_ge_2
  show \<open>?lower \<le> two_l_threshold\<close> by (simp add: nat_le_real_less)

  from
    \<open>threshold \<le> card (set xs)\<close> \<open>l > 0\<close> threshold_ge_2
    power_of_nat_log_le[of 2 \<open>?upper / \<lceil>threshold\<rceil>\<close>]
  show \<open>two_l_threshold \<le> ?upper\<close>
    by (simp add: l_def field_simps nat_le_real_less)
qed

end

interpretation cvm_correctness \<open>nat \<lceil>threshold\<rceil>\<close> 2 \<open>nat l\<close> \<epsilon> xs
  apply unfold_locales
    subgoal by (intro \<epsilon>(1))
    subgoal
      using \<epsilon>(2) \<epsilon>_threshold_ge_12 threshold_ge_2 two_l_threshold_bounds
      apply simp
      using nat_mono threshold_ge_2 by presburger
    done

end

end

end