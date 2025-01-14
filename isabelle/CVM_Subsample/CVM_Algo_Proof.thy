theory CVM_Algo_Proof

imports
  CVM_Algo
  Probabilistic_Prime_Tests.Generalized_Primality_Test
  Negative_Association.Negative_Association_Permutation_Distributions
begin

locale cvm_algo_proof = cvm_algo +
  assumes
    f : \<open>1 / 2 \<le> f\<close> and
    subsample: \<open>subsample_size < threshold\<close>
begin

lemma threshold_pos : \<open>threshold > 0\<close> using subsample by simp
lemma f_le_1: \<open>f \<le> 1\<close> using subsample by (simp add: f_def)

lemma subsample_finite_nonempty:
  assumes \<open>card U \<ge> threshold\<close>
  shows 
    \<open>{T. T \<subseteq> U \<and> card T = subsample_size} \<noteq> {}\<close> (is "?C \<noteq> {}")
    \<open>finite {T. T \<subseteq> U \<and> card T = subsample_size}\<close>
    \<open>finite (set_pmf (subsample U))\<close>
proof -
  have a: \<open>card U choose subsample_size > 0\<close> 
    using subsample assms by (intro zero_less_binomial) auto
  with assms threshold_pos have \<open>card ?C > 0\<close>
    by (metis (mono_tags, lifting) card.infinite n_subsets verit_comp_simplify(3))
    (* unfolding n_subsets[OF assms(1)] by auto *)
  thus \<open>?C \<noteq> {}\<close> \<open>finite ?C\<close> using card_gt_0_iff by blast+
  thus \<open>finite (set_pmf (subsample U))\<close> unfolding subsample_def by auto
qed

(* Lemma 1 *)
lemma int_prod_subsample_eq_prod_int:
  fixes g :: \<open>bool \<Rightarrow> real\<close>
  assumes
    \<open>finite U\<close> \<open>card U = threshold\<close>
    \<open>S \<subseteq> U\<close> \<open>range g \<subseteq> {0..}\<close>
  shows \<open>(\<integral>\<omega>. (\<Prod>s\<in>S. g(s \<in> \<omega>)) \<partial>subsample U) \<le> (\<Prod>s\<in>S. (\<integral>\<omega>. g \<omega> \<partial>bernoulli_pmf f))\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  define \<eta> where \<open>\<eta> = (if g True \<ge> g False then Fwd else Rev)\<close>

  note subsample_finite_nonempty = 
    subsample_finite_nonempty[OF eq_refl[OF assms(2)[symmetric]]]
  let ?C = \<open>{T. T \<subseteq> U \<and> card T = subsample_size}\<close>

  have subssample_size_le_card_U: \<open>subsample_size \<le> card U\<close>
    using subsample unfolding assms(2) by simp

  have na: \<open>measure_pmf.neg_assoc (subsample U) (\<lambda>s \<omega>. of_bool (s \<in> \<omega>)::real) U\<close>
    using subssample_size_le_card_U unfolding subsample_def
    by (intro k_combination_distribution_neg_assoc assms(1))

  note na_imp_prod_mono = has_int_thatD(2)[OF measure_pmf.neg_assoc_imp_prod_mono[OF assms(1) na]]

  define h where \<open>h i \<omega> = (if i \<in> S then g(\<omega> \<ge> (1::real)) else 1::real)\<close> for i \<omega>

  have [split]: \<open>P (\<omega>\<ge>1) = ((\<omega>\<ge>1 \<longrightarrow> P True) \<and> (\<omega> <1 \<longrightarrow> P False))\<close> for P and \<omega> :: real
    unfolding not_le[symmetric] by (metis (full_types))

  have h_borel: \<open>h s \<in> borel_measurable borel\<close> for s unfolding h_def by simp 
  have h_nonneg: \<open>range (h s) \<subseteq> {0..}\<close> for s unfolding h_def using assms(4) by auto
  have h_mono: \<open>monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (h s)\<close> for s unfolding h_def \<eta>_def by (intro monotoneI) auto 

  note [simp] = integrable_measure_pmf_finite[OF subsample_finite_nonempty(3)]

  have c: \<open>map_pmf (\<lambda>\<omega>. s \<in> \<omega>) (subsample U) = bernoulli_pmf f\<close> if \<open>s \<in> U\<close> for s
  proof -
    have \<open>measure (pmf_of_set ?C) {x. s \<notin> x} =
      real (card {T. T\<subseteq>U \<and> card T = subsample_size \<and> s \<notin> T}) / card ?C\<close>
      using subsample_finite_nonempty by (subst measure_pmf_of_set) (simp_all add:Int_def)
    also have \<open>\<dots> = real (card {T. T\<subseteq>(U-{s}) \<and> card T = subsample_size}) / card ?C\<close>
      by (intro arg_cong2[where f="(\<lambda>x y. real (card x)/y)"] Collect_cong) auto
    also have \<open>\<dots> = real(card (U - {s}) choose subsample_size) / real (card U choose subsample_size)\<close>
      using assms(1) by (subst (1 2) n_subsets) auto
    also have \<open>\<dots> = real((threshold - 1) choose subsample_size) 
      / real (threshold choose subsample_size)\<close>
      using assms(2) that by simp
    also have \<open>\<dots> = real(threshold *((threshold-1) choose subsample_size))
      / real (threshold * (threshold choose subsample_size))\<close>
      using threshold_pos by simp
    also have \<open>\<dots> = real (threshold - subsample_size) / real threshold\<close>
      unfolding binomial_absorb_comp[symmetric] using subsample by simp
    also have \<open>\<dots> = (real threshold - real subsample_size) / real threshold\<close>
      using subsample by (subst of_nat_diff) auto
    also have \<open>\<dots> = 1-f\<close> using threshold_pos f_def by (simp add:field_simps)
    finally have \<open>1-measure (pmf_of_set ?C) {x. s \<notin> x} = f\<close> by simp

    hence \<open>measure (pmf_of_set ?C) {x. s \<in> x} = f\<close>
      by (subst (asm) measure_pmf.prob_compl[symmetric]) (auto simp:diff_eq Compl_eq) 
    thus ?thesis by (intro eq_bernoulli_pmfI) (simp add: pmf_map vimage_def subsample_def)
  qed

  have \<open>?L = (\<integral>\<omega>. (\<Prod>s\<in>U. h s (of_bool(s \<in> \<omega>))) \<partial>subsample U)\<close> unfolding h_def
    by (intro arg_cong2[where f="integral\<^sup>L"] refl ext prod.mono_neutral_cong_left assms(1,3)) auto
  also have \<open>\<dots> \<le> (\<Prod>s\<in>U. (\<integral>\<omega>. h s (of_bool(s \<in> \<omega>)) \<partial>subsample U))\<close>
    by (intro na_imp_prod_mono[OF _ h_mono] h_borel h_nonneg) auto
  also have \<open>\<dots> = (\<Prod>s\<in>S. (\<integral>\<omega>. g(s \<in> \<omega>) \<partial>subsample U))\<close> unfolding h_def 
    by (intro prod.mono_neutral_cong_left[symmetric] assms(1,3)) 
      (auto intro!:arg_cong[where f=\<open>integral\<^sup>L (subsample U)\<close>]) 
  also have \<open>\<dots> = (\<Prod>s\<in>S. (\<integral>\<omega>. g \<omega> \<partial>map_pmf (\<lambda>\<omega>. s \<in> \<omega>) (subsample U)))\<close> by simp
  also have \<open>\<dots> = ?R\<close> using c assms(3) by (intro prod.cong refl) (metis in_mono)
  finally show ?thesis by simp
qed

(* Copied as-is for Lemma 2 *)
context
  fixes \<phi> :: \<open>real \<Rightarrow> bool \<Rightarrow> real\<close>
  assumes phi : 
    \<open>\<And> x b. \<lbrakk>0 < x; x \<le> 1\<rbrakk> \<Longrightarrow> \<phi> x b \<ge> 0\<close>
    \<open>\<And> p x.
      \<lbrakk>0 < p; p < 1; 0 < x; x \<le> 1\<rbrakk> \<Longrightarrow>
      measure_pmf.expectation (bernoulli_pmf p) (\<phi> x) \<le> \<phi> (x / p) True\<close>
    \<open>\<And> x y.
      \<lbrakk>0 < x; x \<le> y; y \<le> 1\<rbrakk> \<Longrightarrow>
      \<phi> x False \<le> \<phi> y False\<close>
begin

abbreviation (input)
  \<open>aux \<equiv> \<lambda> x state. \<phi> (f ^ (state_k state)) (x \<in> (state_chi state))\<close>

(*
  Intuition:
  - U is the set of elements we have already seen
  - st is the accumulated PMF so far
  - We know:
    state_k st \<le> n where n is the number of list elements
    state_chi st \<subseteq> U
*)

context
  fixes state :: \<open>('a, 'b) state_scheme pmf\<close>
  assumes state_finite_support : \<open>finite <| set_pmf state\<close>
begin

lemma step_1_preserves_finite_support :
  \<open>finite <| set_pmf <| state \<bind> step_1 x'\<close>
  by (simp flip: map_pmf_def add: state_finite_support step_1_def)

private method simps = (
  simp
    flip: map_pmf_def
    add: step_1_def pmf_expectation_bind power_le_one Let_def,
  simp add: integral_measure_pmf algebra_simps,
  intro sum.cong[OF refl])

lemma step_1_preserves_expectation_le :
  assumes
    \<open>finite U\<close>
    \<open>\<And> S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation state (\<lambda> state. \<Prod> x \<in> S. aux x state)
      \<le> (\<phi> 1 True) ^ card S\<close>
    (is \<open>\<And> S. _ \<Longrightarrow> ?L' S \<le> _\<close>)
    \<open>S \<subseteq> insert x' U\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step_1 x') (\<lambda> state. \<Prod> x \<in> S. aux x state)
    \<le> (\<phi> 1 True) ^ card S\<close>
    (is \<open>?L \<le> ?R\<close>)
proof (cases \<open>x' \<in> S\<close>)
  case False
  moreover note assms

  moreover from calculation state_finite_support f f_le_1
  have \<open>?L = ?L' S\<close>
    apply simps
    by (smt (verit, best) prod.cong)

  ultimately show ?thesis by auto
next
  case True
  with assms state_finite_support f f_le_1 have
    \<open>?L = (\<Sum> s \<in> set_pmf state.
      pmf state s * (\<Prod> x \<in> S - {x'}. \<phi> (f ^ state_k s) (x \<in> state_chi s)) * (
        measure_pmf.expectation (bernoulli_pmf <| f ^ state_k s) (\<phi> <| f ^ state_k s) ))\<close>
    (is \<open>_ = ?L'' (\<lambda> _ :: (_, _) state_scheme. measure_pmf.expectation _ _)\<close>)
    apply simps
    by (smt (verit, best) Diff_iff finite.intros(2) insertCI prod.cong prod.remove rev_finite_subset)

  also from f f_le_1 phi have \<open>\<dots> \<le> ?L'' \<lblot>\<phi> 1 True\<rblot>\<close>
    apply (intro sum_mono)
    apply (simp flip: pmf_positive_iff)
    by (smt (z3) div_by_1 divide_self_if integral_bernoulli_pmf landau_omega.R_mult_left_mono nonzero_mult_div_cancel_right power_le_one prod_nonneg zero_compare_simps(6)
      zero_less_power)

  also from assms \<open>x' \<in> S\<close> state_finite_support phi
  have \<open>\<dots> \<le> \<phi> 1 True ^ (card S - 1) * \<phi> 1 True\<close>
    apply (simp flip: sum_distrib_right add: integral_measure_pmf)
    by (smt (verit, best) One_nat_def card_Diff_singleton landau_omega.R_mult_right_mono subset_insert_iff sum.cong)

  finally show ?thesis
    using assms \<open>x' \<in> S\<close>
    by (metis (lifting) Groups.mult_ac(2) Suc_diff_1 bot_nat_0.extremum card_0_eq empty_iff finite_insert infinite_super le_eq_less_or_eq power.simps(2))
qed

end

context
  fixes state :: \<open>('a, 'b) state_scheme pmf\<close>
  assumes state_finite_support : \<open>finite <| set_pmf state\<close>
begin

lemma step_2_preserves_finite_support :
  \<open>finite <| set_pmf <| state \<bind> step_2\<close>
  using state_finite_support subsample_finite_nonempty
  by (auto simp add: step_2_def subsample_def Let_def not_less)

lemma step_2_preserves_expectation_le :
  assumes
    \<open>finite U\<close>
    \<open>measure_pmf.expectation state (prod aux S) \<le> (\<phi> 1 True) ^ card S\<close>
    \<open>S \<subseteq> U\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step_2) (\<lambda> state. \<Prod> x \<in> S. aux x state)
    \<le> (\<phi> 1 True) ^ card S\<close>
proof -
  from assms step_2_preserves_finite_support state_finite_support show ?thesis
    apply (simp add: step_2_def pmf_expectation_bind integral_measure_pmf Let_def)
    unfolding if_distrib if_distribR
    apply (simp add: sum.If_cases)
    sorry
qed

lemma step_preserves_expectation_le :
  assumes
    \<open>finite U\<close>
    \<open>\<And> S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation state (\<lambda> state. \<Prod> x \<in> S. aux x state)
      \<le> (\<phi> 1 True) ^ card S\<close>
    \<open>S \<subseteq> insert x U\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step x) (\<lambda> state. \<Prod> x \<in> S. aux x state)
    \<le> (\<phi> 1 True) ^ card S\<close>
proof -
  show ?thesis sorry
qed

lemma run_steps_preserves_expectation_le :
  assumes \<open>S \<subseteq> set xs\<close>
  shows
    \<open>measure_pmf.expectation (run_steps xs) (\<lambda> state. \<Prod> x \<in> S. aux x state)
    \<le> (\<phi> 1 True) ^ card S\<close>
proof -
  show ?thesis sorry
qed

(* Run some prefix of the elements + one more *)
lemma run_steps_then_step_1_preserves_expectation_le :
  assumes
    \<open>S \<subseteq> insert x' (set xs)\<close>
  shows
    \<open>measure_pmf.expectation (run_steps xs \<bind> step_1 x') (\<lambda> state. \<Prod> x \<in> S. aux x state)
    \<le> \<phi> 1 True ^ card S\<close>
proof -
  show ?thesis sorry
qed

end

context
  fixes q :: real and h :: \<open>real \<Rightarrow> real\<close>
  assumes
    \<open>0 < q\<close> \<open>q \<le> 1\<close> and
    \<open>concave_on {0 .. 1 / q} h\<close> and
    \<open>\<And> x. \<lbrakk>1 \<le> x; x * q \<le> 1\<rbrakk> \<Longrightarrow> h x \<ge> 0\<close>
begin

abbreviation (input)
  \<open>aux' \<equiv> \<lambda> x state. (
    let p = f ^ (state_k state)
    in of_bool (p > q) * h ((1 / p) * indicat_real (state_chi state) x))\<close>

(* Lemma 3 *)
lemma run_steps_preserves_expectation_le' :
  assumes \<open>S \<subseteq> set xs\<close>
  shows
    \<open>measure_pmf.expectation (run_steps xs) (\<lambda> state. \<Prod> x \<in> S. aux' x state) \<le> (h 1) ^ card S\<close>
proof -
  show ?thesis sorry
qed

end

end (* end cvm_algo_proof *)

end (* end theory *)
