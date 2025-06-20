section \<open>Instantiation of main CVM correctness theorem\<close>

text
  \<open>The main result here is \texttt{prob\_cvm\_incorrect\_le\_delta}, which
  formalises the correctness part of Theorem 2 of \cite{cvm_2023}.
  
  In fact, our result is stronger, as we provide the same correctness guarantee
  using a smaller threshold of
  $\lceil \frac{12}{\varepsilon^2} \text{log}_2 \frac{3m}{\delta} \rceil$
  where $m$ is the length of the input list.
  
  Our result also formalises the intuitive observation that this holds for all
  choices of thresholds that are at least this value.\<close>

theory CVM_Correctness_Instance

imports
  CVM_Correctness

begin

subsection \<open>Auxiliary arithmetic lemma\<close>

lemma exp_minus_log_le :
  assumes \<open>9/8 \<le> a\<close> \<open>2 \<le> b\<close> \<open>0 < c\<close> \<open>c \<le> 1\<close>
  shows \<open>exp (- a * log 2 (3 * b / c)) \<le> 2*c / (15 * b)\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  have \<open>?L \<le> exp (- (9/8) * log 2 (3 * b / c))\<close> using assms
    by (intro iffD2[OF exp_le_cancel_iff] mult_right_mono iffD2[OF zero_le_log_cancel_iff]) auto

  also have \<open>\<dots> = exp (log 2 (1 / (3 * b / c)) * 9/8)\<close>
    unfolding log_recip by simp

  also have \<open>\<dots> = exp (ln (c / (3 * b)) * 9/(8*ln 2))\<close>
    unfolding log_def by (simp add: divide_simps)

  also from assms have \<open>\<dots> = ((1-2*c/b) *\<^sub>R 0 + (2*c /b) *\<^sub>R (1/6)) powr (9/(8*ln 2))\<close>
    unfolding powr_def by (auto simp: algebra_simps)

  also from assms ln_2_less_1
  have \<open>\<dots> \<le> (1-2*c/b) * 0 powr (9/(8*ln 2)) + (2*c /b) * (1/6) powr (9/(8*ln 2))\<close>
    apply (intro convex_onD[OF convex_powr]) by simp_all

  also have \<open>\<dots> = (c/b) * (2*(1/6) powr (9/(8*ln 2)))\<close> (is \<open>_ = _ * ?x\<close>) by simp

  also have \<open>\<dots> \<le> (c/b) * (2/15)\<close> (is \<open>_ \<le> _ * ?y\<close>)
  proof (intro mult_left_mono)
    from assms show \<open>c / b \<ge> 0\<close> by simp
    show \<open>?x \<le> ?y\<close> by (approximation 7)
  qed

  also have \<open>\<dots> = ?R\<close> by simp

  finally show ?thesis .
qed

subsection \<open>Instantiating the main correctness theorem\<close>

text
  \<open>Here we instantiate the main correctness theorem
  \texttt{prob\_cvm\_incorrect\_le} with a threshold that is
  $\ge \lceil \frac{12}{\varepsilon^2} \text{log}_2 \frac{3 * m}{\delta} \rceil$
  
  Note that this result provides an API that allows us to assume without loss of
  generality that \texttt{xs} $\ne$ \texttt{[]} and
  \texttt{threshold} $\le$ \texttt{card (set xs)}
  where \texttt{xs} is the input list.\<close>

context
  fixes
    \<epsilon> \<delta> threshold :: real and
    xs :: \<open>'a list\<close>
begin

abbreviation \<open>length_xs_1 \<equiv> max (Suc 0) (length xs)\<close>

definition \<open>l \<equiv> \<lfloor>log 2 <| 4 * card (set xs) / \<lceil>threshold\<rceil>\<rfloor>\<close>

context
  assumes
    \<epsilon> : \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> and
    \<delta> : \<open>0 < \<delta>\<close> \<open>\<delta> \<le> 1\<close> and
    threshold : \<open>threshold \<ge> 12 / \<epsilon>\<^sup>2 * log 2 (3 * length_xs_1 / \<delta>)\<close>
begin

interpretation cvm_error_bounds \<open>nat \<lceil>threshold\<rceil>\<close> 2 \<open>nat l\<close> \<epsilon> xs .

context
  assumes \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close>
begin

lemma ceil_threshold_ge_2 :
  \<open>\<lceil>threshold\<rceil> \<ge> 2\<close>
  using \<epsilon> \<delta> threshold \<open>xs \<noteq> []\<close>
  apply simp
  by (smt (verit, best) Num.of_nat_simps(2) approximation_preproc_nat(8) divide_le_eq_1_pos log_divide_pos log_le_one_cancel_iff log_le_zero_cancel_iff numeral_nat(7)
    power2_nonneg_gt_1_iff zero_less_power)

lemma epsilon_ceil_threshold_ge_12 :
  \<open>\<epsilon>\<^sup>2 * \<lceil>threshold\<rceil> \<ge> 12\<close>
  using \<epsilon> \<delta> threshold \<open>xs \<noteq> []\<close>
  apply (simp add: field_simps)
  by (smt (verit, ccfv_SIG) Groups.mult_ac(2) Num.of_nat_simps(2) approximation_preproc_nat(8) ceiling_divide_upper log_divide_pos log_le_one_cancel_iff log_le_zero_cancel_iff
    nonzero_mult_div_cancel_left numeral_nat(7) zero_less_power)

lemma two_l_threshold_bounds :
  \<open>2 * card (set xs) \<le> two_l_threshold\<close> (is \<open>?lower \<le> _\<close>)
  \<open>two_l_threshold \<le> 4 * card (set xs)\<close> (is \<open>_ \<le> ?upper\<close>)
proof -
  note assms = \<open>threshold \<le> card (set xs)\<close> ceil_threshold_ge_2

  from assms have \<open>l > 0\<close> by (simp add: l_def field_simps) linarith

  with assms have \<open>log 2 ?lower \<le> log 2 two_l_threshold\<close>
    apply (simp add: l_def log_mult_pos log_divide_pos)
    by (smt (z3) Num.of_nat_simps(2,4) four_x_squared log2_of_power_eq nat_1_add_1 of_nat_power one_power2 real_of_int_floor_add_one_ge)

  with assms show \<open>?lower \<le> two_l_threshold\<close> by (simp add: nat_le_real_less)

  from assms \<open>l > 0\<close> show \<open>two_l_threshold \<le> ?upper\<close>
    apply (simp add: l_def nat_le_real_less)
    by (smt (verit, best) pos_le_divide_eq power_of_nat_log_le zero_compare_simps(8) zero_less_power)
qed

text \<open>The next result is analogous to claim 3 of \cite{cvm_2023}.\<close>

lemma prob_fail_bound_le_delta :
  \<open>prob_fail_bound \<le> \<delta> / 3\<close>
  using \<epsilon> \<delta> threshold ceil_threshold_ge_2 \<open>xs \<noteq> []\<close>
  unfolding prob_bounds_defs
  apply (simp add: divide_simps)
  by (smt (verit, ccfv_SIG) approximation_preproc_nat(8) divide_le_eq_1_pos le_log_of_power nonzero_mult_div_cancel_left pos_le_divide_eq power_le_one_iff real_nat_ceiling_ge)

lemma length_ge_2 :
  \<open>length xs \<ge> 2\<close>
  using threshold ceil_threshold_ge_2 \<open>xs \<noteq> []\<close> \<open>threshold \<le> card (set xs)\<close> 
  apply simp
  by (metis Suc_1 leD not_less_eq_eq of_nat_1_eq_iff rotate1_fixpoint_card rotate1_length01)

text
  \<open>\texttt{prob\_k\_gt\_l\_bound\_le\_delta} and
  \texttt{prob\_k\_le\_l\_and\_est\_out\_of\_range\_bound\_le\_delta}
  are analogous to claim 4 of \cite{cvm_2023}.\<close>

lemma prob_k_gt_l_bound_le_delta :
  \<open>prob_k_gt_l_bound \<le> 2 * \<delta> / 15\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  have \<open>?L \<le> length xs * exp (- threshold / 6)\<close>
    unfolding prob_bounds_defs
    by (simp add: divide_simps mult_left_mono real_nat_ceiling_ge)

  also from threshold length_ge_2
  have \<open>\<dots> \<le> real (length xs) * exp (- (2 / \<epsilon>\<^sup>2) * log 2 (3 * real length_xs_1 / \<delta>))\<close>
    by (auto intro: mult_left_mono)

  also have \<open>\<dots> \<le> length xs * (2 * \<delta> / (15 * real length_xs_1))\<close>
  proof -
   from \<epsilon> have \<open>9 / 8 \<le> 2 / \<epsilon>\<^sup>2\<close>
     apply (simp add: divide_simps)
     by (smt (z3) power_le_one_iff)

   with \<epsilon> \<delta> length_ge_2 show ?thesis
     apply (intro mult_left_mono exp_minus_log_le) by simp_all 
  qed

  also from \<delta> have \<open>\<dots> \<le> ?R\<close> by (simp add: divide_simps)

  finally show ?thesis .
qed

lemma prob_k_le_l_and_est_out_of_range_bound_le_delta :
  \<open>prob_k_le_l_and_est_out_of_range_bound \<le> 8 * \<delta> / 15\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  from \<epsilon> have \<open>?L \<le> 4 * exp (-\<epsilon>\<^sup>2 * threshold / (8 * (1 + \<epsilon> / 3)))\<close>
    unfolding prob_bounds_defs
    apply (simp add: field_simps)
    by (simp add: add_mono_thms_linordered_semiring(1) real_nat_ceiling_ge)

  also from \<epsilon> threshold
  have \<open>\<dots> \<le> 4 * exp (- (12 / (8 * (1 + \<epsilon> / 3))) * log 2 (3 * real length_xs_1 / \<delta>))\<close>
    by (simp add: divide_simps)

  also from \<epsilon> \<delta> length_ge_2
  have \<open>\<dots> \<le> 4 * (2 * \<delta> / (15 * real length_xs_1))\<close>
    apply (intro mult_left_mono exp_minus_log_le) by (simp_all add: divide_simps)

  also from \<delta> have \<open>\<dots> \<le> ?R\<close> by (simp add: field_simps)

  finally show ?thesis .
qed

end

text \<open>Main correctness instantiation result.\<close>

theorem prob_cvm_incorrect_le_delta :
  \<open>\<P>(estimate in cvm xs.
    estimate |> is_None_or_pred (\<lambda> estimate. estimate >[\<epsilon>] card (set xs)))
  \<le> \<delta>\<close>
  apply (intro prob_cvm_incorrect_le)
  using
    \<epsilon> \<delta> epsilon_ceil_threshold_ge_12 ceil_threshold_ge_2 two_l_threshold_bounds
    prob_fail_bound_le_delta prob_k_gt_l_bound_le_delta
    prob_k_le_l_and_est_out_of_range_bound_le_delta
  by simp_all linarith

end

thm prob_cvm_incorrect_le_delta[simplified]

end

end