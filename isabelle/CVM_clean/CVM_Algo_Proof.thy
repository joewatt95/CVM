theory CVM_Algo_Proof

imports
  CVM_Algo
  Probabilistic_Prime_Tests.Generalized_Primality_Test
  Negative_Association.Negative_Association_Permutation_Distributions
begin

locale cvm_algo_proof = cvm_algo +
  assumes f : \<open>1 / 2 \<le> f\<close> \<open>f < 1\<close> \<open>n * f \<in> \<nat>\<close>
begin                       

(* Lemma 1 *)
lemma int_prod_subsample_eq_prod_int:
  fixes g :: \<open>bool \<Rightarrow> real\<close>
  assumes
    \<open>finite U\<close> \<open>card U = n\<close>
    \<open>S \<subseteq> U\<close> \<open>range g \<subseteq> {0..}\<close>
  shows \<open>(\<integral>\<omega>. (\<Prod>s\<in>S. g(s \<in> \<omega>)) \<partial>subsample U) \<le> (\<Prod>s\<in>S. (\<integral>\<omega>. g \<omega> \<partial>bernoulli_pmf f))\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  obtain k where k_eq: \<open>real k = real n * f\<close> by (metis f(3) Nats_cases)
  define \<eta> where \<open>\<eta> = (if g True \<ge> g False then Fwd else Rev)\<close>

  let ?C = "{T. T \<subseteq> U \<and> card T = k}"

  have subsample_eq: \<open>subsample U = pmf_of_set ?C\<close>
    unfolding subsample_def k_eq[symmetric] by auto

  have k_le_n: \<open>real k \<le> real n\<close>
    using f(2) by (simp add: mult_le_cancel_right2 mult_of_nat_commute k_eq)
  hence k_le_card_U: \<open>k \<le> card U\<close>
    unfolding assms(2) by simp

  have a: \<open>card U choose k > 0\<close> by (intro zero_less_binomial k_le_card_U)
  hence \<open>card ?C > 0\<close> unfolding n_subsets[OF assms(1)] by (intro zero_less_binomial k_le_card_U)
  hence b: \<open>?C \<noteq> {} \<and> finite ?C\<close> using card_gt_0_iff by blast

  have na: \<open>measure_pmf.neg_assoc (subsample U) (\<lambda>s \<omega>. of_bool (s \<in> \<omega>)::real) U\<close>
    using k_le_card_U unfolding subsample_eq 
    by (intro k_combination_distribution_neg_assoc assms(1))

  note na_imp_prod_mono = has_int_thatD(2)[OF measure_pmf.neg_assoc_imp_prod_mono[OF assms(1) na]]

  define h where \<open>h i \<omega> = (if i \<in> S then g(\<omega> \<ge> (1::real)) else 1::real)\<close> for i \<omega>

  have [split]: \<open>P (\<omega>\<ge>1) = ((\<omega>\<ge>1 \<longrightarrow> P True) \<and> (\<omega> <1 \<longrightarrow> P False))\<close> for P and \<omega> :: real
    unfolding not_le[symmetric] by (metis (full_types))

  have h_borel: \<open>h s \<in> borel_measurable borel\<close> for s unfolding h_def by simp 
  have h_nonneg: \<open>range (h s) \<subseteq> {0..}\<close> for s unfolding h_def using assms(4) by auto
  have h_mono: \<open>monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (h s)\<close> for s unfolding h_def \<eta>_def by (intro monotoneI) auto 
  have "finite (set_pmf (subsample U))"
    using b unfolding subsample_eq by simp
  note [simp] = integrable_measure_pmf_finite[OF this]

  have c: \<open>map_pmf (\<lambda>\<omega>. s \<in> \<omega>) (subsample U) = bernoulli_pmf f\<close> if \<open>s \<in> U\<close> for s
  proof -
    have n_gt_0: \<open>n > 0\<close> using that assms(1,2) card_gt_0_iff by blast

    have \<open>measure (pmf_of_set ?C) {x. s \<notin> x} = real (card {T. T\<subseteq>U \<and> card T = k \<and> s \<notin> T}) / card ?C\<close>
      using b by (subst measure_pmf_of_set) (simp_all add:Int_def)
    also have \<open>\<dots> = real (card {T. T\<subseteq>(U-{s}) \<and> card T = k}) / card ?C\<close>
      by (intro arg_cong2[where f="(\<lambda>x y. real (card x)/y)"] Collect_cong) auto
    also have \<open>\<dots> = real(card (U - {s}) choose k) / real (card U choose k)\<close>
      using assms(1) by (subst (1 2) n_subsets) auto
    also have \<open>\<dots> = real((n - 1) choose k) / real (n choose k)\<close>
      using assms(2) that by simp
    also have \<open>\<dots> = real(n * ((n - 1) choose k)) / real (n * (n choose k))\<close>
      using n_gt_0 by simp 
    also have \<open>\<dots> = real (n - k) / real n\<close> unfolding binomial_absorb_comp[symmetric] using a by simp
    also have \<open>\<dots> = (real n - real k) / real n\<close> using k_le_n by (subst of_nat_diff) auto
    also have \<open>\<dots> = 1-f\<close> using n_gt_0 unfolding k_eq by (simp add:field_simps)
    finally have \<open>1-measure (pmf_of_set ?C) {x. s \<notin> x} = f\<close> by simp

    hence \<open>measure (pmf_of_set ?C) {x. s \<in> x} = f\<close>
      by (subst (asm) measure_pmf.prob_compl[symmetric]) (auto simp:diff_eq Compl_eq) 
    thus ?thesis by (intro eq_bernoulli_pmfI) (simp add: pmf_map vimage_def subsample_eq)
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
    \<open>\<And> x b. \<lbrakk>0 < x; x \<le> 1\<rbrakk> \<Longrightarrow> \<phi> x b \<ge> 0\<close> and
    \<open>\<And> \<alpha> x.
      \<lbrakk>0 < \<alpha>; \<alpha> < 1; 0 < x; x \<le> 1\<rbrakk> \<Longrightarrow>
      (1 - \<alpha>) * \<phi> x False + \<alpha> * \<phi> x True \<le> \<phi> (x / \<alpha>) True \<close> and
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

lemma step_1_preserves_expectation_le :
  assumes
    \<open>finite U\<close>
    \<open>\<And> S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation state (\<Prod> x \<in> S. aux x) \<le> (\<phi> 1 True) ^ card S\<close>
    \<open>S \<subseteq> insert x U\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step_1 x) (\<Prod> x \<in> S. aux x)
    \<le> (\<phi> 1 True) ^ card S\<close>
proof - 
  show ?thesis sorry
qed

lemma step_2_preserves_expectation_le :
  assumes
    \<open>finite U\<close>
    \<open>measure_pmf.expectation state (prod aux S) \<le> (\<phi> 1 True) ^ card S\<close>
    \<open>S \<subseteq> U\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step_2) (\<Prod> x \<in> S. aux x)
    \<le> (\<phi> 1 True) ^ card S\<close>
proof - 
  show ?thesis sorry
qed

lemma step_preserves_expectation_le :
  assumes
    \<open>finite U\<close>
    \<open>\<And> S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation state (\<Prod> x \<in> S. aux x) \<le> (\<phi> 1 True) ^ card S\<close>
    \<open>S \<subseteq> insert x U\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step x) (\<Prod> x \<in> S. aux x)
    \<le> (\<phi> 1 True) ^ card S\<close>
proof - 
  show ?thesis sorry
qed

lemma expectation_cvm:
  assumes
    \<open>finite U\<close>
    \<open>\<And>S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation state (prod aux S) \<le> (\<phi> 1 True) ^ card S\<close>
  assumes \<open>S \<subseteq> set xs \<union> U\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> run_steps xs) (\<Prod> x \<in> S. aux x)
    \<le> (\<phi> 1 True) ^ card S\<close>
proof - 
  show ?thesis sorry
qed

(* Run some prefix of the elements + one more *)
lemma run_steps_then_step_1_preserves_expectation_le :
  assumes
    \<open>finite U\<close>
    \<open>\<And>S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation state (\<Prod> x \<in> S. aux x) \<le> (\<phi> 1 True) ^ card S\<close>
    \<open>S \<subseteq> insert x (set xs \<union> U)\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> run_steps xs \<bind> step_1 x) (\<Prod> x \<in> S. aux x)
    \<le> (\<phi> 1 True) ^ card S\<close>
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
lemma expectation_cvm' :
  assumes U: \<open>finite U\<close>
  assumes \<open>\<And> S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation stp (prod aux' S) \<le> (h 1) ^ card S\<close>
  assumes \<open>S \<subseteq> set xs \<union> U\<close>
  shows
    \<open>measure_pmf.expectation (stp \<bind> cvm xs) (prod aux2 S) \<le> (h 1) ^ card S\<close>
proof -
  show ?thesis sorry
qed

end

end (* end cvm_algo_proof *)

end (* end theory *)
