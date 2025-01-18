theory CVM_Algo_Proof

imports
  Probabilistic_Prime_Tests.Generalized_Primality_Test
  Negative_Association.Negative_Association_Permutation_Distributions
  CVM_Subsample.CVM_Algo
  "HOL-Decision_Procs.Approximation"
begin

lemma bounded_finite:
  assumes "finite S"
  shows "bounded (f ` S)"
  using assms by (intro finite_imp_bounded) auto

lemma of_bool_power:
  assumes \<open>y > 0\<close>
  shows \<open>((of_bool x)::real) ^ (y::nat) = of_bool x\<close>
  by (simp add: assms)

datatype 'a run_state = FinalState \<open>'a list\<close> | IntermState \<open>'a list\<close> \<open>'a\<close>

lemma run_state_induct:
  assumes \<open>P (FinalState [])\<close>
  assumes \<open>\<And>xs x. P (FinalState xs) \<Longrightarrow> P (IntermState xs x)\<close>
  assumes \<open>\<And>xs x. P (IntermState xs x) \<Longrightarrow> P (FinalState (xs@[x]))\<close>
  shows \<open>P result\<close>
proof -
  have \<open>P (FinalState xs) \<and> P (IntermState xs x)\<close> for xs x
    using assms by (induction xs rule:rev_induct) auto
  thus ?thesis by (cases result) auto
qed

locale cvm_algo_proof = cvm_algo +
  assumes
    f : \<open>1 / 2 \<le> f\<close> and
    subsample : \<open>subsample_size < threshold\<close>
begin

definition \<open>state_p \<omega> = f ^ state_k \<omega>\<close>

lemma threshold_pos : \<open>threshold > 0\<close> using subsample by simp
lemma f_lt_1 : \<open>f < 1\<close> using subsample by (simp add: f_def)
lemma f_le_1 : \<open>f \<le> 1\<close> using subsample by (simp add: f_def)

lemma run_steps_snoc: \<open>run_steps (xs @[x]) = run_steps xs \<bind> step_1 x \<bind> step_2\<close>
  unfolding run_steps_def foldM_pmf_snoc step_def by (simp add:bind_assoc_pmf)

lemma subsample_finite_nonempty:
  assumes \<open>card U \<ge> threshold\<close>
  shows
    \<open>{T. T \<subseteq> U \<and> card T = subsample_size} \<noteq> {}\<close> (is \<open>?C \<noteq> {}\<close>)
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

fun run_state_pmf where
  \<open>run_state_pmf (FinalState xs) = run_steps xs\<close> |
  \<open>run_state_pmf (IntermState xs x) = run_steps xs \<bind> step_1 x\<close>

fun len_run_state where
  \<open>len_run_state (FinalState xs) = length xs\<close> |
  \<open>len_run_state (IntermState xs x) = length xs\<close>

fun run_state_set where
  \<open>run_state_set (FinalState xs) = set xs\<close> |
  \<open>run_state_set (IntermState xs x) = set xs \<union> {x}\<close>

fun max_card_state where
  \<open>max_card_state (FinalState _) = threshold - 1\<close> |
  \<open>max_card_state (IntermState _ _) = threshold\<close>

lemma finite_run_state_set[simp]: \<open>finite (run_state_set \<sigma>)\<close> by (cases \<sigma>) auto

lemma step_2_preserves_finite_support :
  assumes \<open> (finite (set_pmf state))\<close>
  shows \<open>finite <| set_pmf <| state \<bind> step_2\<close>
  using assms subsample_finite_nonempty
  by (auto simp add: step_2_def subsample_def Let_def not_less)

lemma finite_run_state_pmf: \<open>finite (set_pmf (run_state_pmf \<sigma>))\<close>
proof (induction \<sigma> rule:run_state_induct)
  case 1 thus ?case by (simp add:run_steps_def)
next
  case (2 xs x) thus ?case by (simp add:step_1_def)
next
  case (3 xs x)
  have a: \<open>run_state_pmf (FinalState (xs@[x])) = run_state_pmf (IntermState xs x) \<bind> step_2\<close>
    by (simp add:run_steps_snoc)
  show ?case unfolding a using step_2_preserves_finite_support[OF 3] by simp
qed

lemma state_chi_run_state_pmf:
  fixes \<sigma> :: \<open>'a run_state\<close>
  shows \<open>AE \<omega> in run_state_pmf \<sigma>. state_chi \<omega> \<subseteq> run_state_set \<sigma>\<close>
proof (induction \<sigma> rule:run_state_induct)
  case 1 thus ?case by (simp add:run_steps_def AE_measure_pmf_iff initial_state_def)
next
  case (2 xs x)
  then show ?case by (simp add:AE_measure_pmf_iff step_1_def remove_def) auto
next
  case (3 xs x)
  let ?p = \<open>run_state_pmf (IntermState xs x)\<close>
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = ?p \<bind> step_2\<close>
    by (simp add:run_steps_snoc)

  have \<open>AE \<omega> in subsample U. \<omega> \<subseteq> U\<close> if \<open>\<not>card U < threshold\<close> for  U :: \<open>'a set\<close>
  proof -
    have \<open>card U \<ge> threshold\<close> using that by simp
    from subsample_finite_nonempty[OF this]
    show ?thesis unfolding subsample_def by (auto simp:AE_measure_pmf_iff)
  qed
  thus ?case unfolding b using 3 by (simp add:AE_measure_pmf_iff step_2_def Let_def) blast
qed

lemma card_run_state_pmf:
  fixes \<sigma> :: \<open>'a run_state\<close>
  shows \<open>AE \<omega> in run_state_pmf \<sigma>. card (state_chi \<omega>) \<le> max_card_state \<sigma>\<close>
proof (induction \<sigma> rule:run_state_induct)
  case 1
  then show ?case by (simp add:AE_measure_pmf_iff run_steps_def initial_state_def)
next
  case (2 xs x)
  have \<open>card (insert x S) \<le> threshold \<and> card (Set.remove x S) \<le> threshold\<close>
    if \<open>card S \<le> threshold - 1\<close> for S using threshold_pos that
    by (metis card_Diff1_le diff_le_self order.trans remove_def card_insert_le_m1)
  thus ?case using 2 by (auto simp add:AE_measure_pmf_iff step_1_def)
next
  case (3 xs x)
  let ?p = \<open>run_state_pmf (IntermState xs x)\<close>
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = ?p \<bind> step_2\<close>
    by (simp add:run_steps_snoc)

  have \<open>AE \<omega> in subsample U. card \<omega> = subsample_size\<close> if \<open>\<not>card U < threshold\<close> for U :: \<open>'a set\<close>
  proof -
    have \<open>card U \<ge> threshold\<close> using that by simp
    from subsample_finite_nonempty[OF this]
    show ?thesis unfolding subsample_def by (auto simp:AE_measure_pmf_iff)
  qed
  moreover have \<open>subsample_size \<le> threshold - 1\<close>
    using threshold_pos subsample by simp
  ultimately show ?case
    unfolding b AE_measure_pmf_iff set_bind_pmf by (auto simp: step_2_def Let_def)
qed

(* Lemma 1 *)
lemma int_prod_subsample_eq_prod_int:
  fixes g :: \<open>bool \<Rightarrow> real\<close>
  assumes
    \<open>finite U\<close> \<open>card U = threshold\<close>
    \<open>S \<subseteq> U\<close> \<open>range g \<subseteq> {0..}\<close>
  shows \<open>(\<integral>\<omega>. (\<Prod>s\<in>S. g(s \<in> \<omega>)) \<partial>subsample U) \<le> (\<Prod>s\<in>S. (\<integral>\<omega>. g \<omega> \<partial>bernoulli_pmf f))\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  define \<eta> where \<open>\<eta> \<equiv> if g True \<ge> g False then Fwd else Rev\<close>

  note subsample_finite_nonempty =
    subsample_finite_nonempty[OF eq_refl[OF assms(2)[symmetric]]]

  note [simp] = integrable_measure_pmf_finite[OF subsample_finite_nonempty(3)]

  let ?C = \<open>{T. T \<subseteq> U \<and> card T = subsample_size}\<close>

  have subssample_size_le_card_U: \<open>subsample_size \<le> card U\<close>
    using subsample unfolding assms(2) by simp

  have \<open>measure_pmf.neg_assoc (subsample U) (\<lambda>s \<omega>. (s \<in> \<omega>)) U\<close>
    using subssample_size_le_card_U unfolding subsample_def
    by (intro n_subsets_distribution_neg_assoc assms(1))

  hence na: \<open>measure_pmf.neg_assoc (subsample U) (\<lambda>s \<omega>. (s \<in> \<omega>)) S\<close>
    using measure_pmf.neg_assoc_subset[OF assms(3)] by auto

  have fin_S: \<open>finite S\<close> using assms(1,3) finite_subset by auto
  note na_imp_prod_mono = has_int_thatD(2)[OF measure_pmf.neg_assoc_imp_prod_mono[OF fin_S na]]

  have g_borel: \<open>g \<in> borel_measurable borel\<close> by (intro borel_measurable_continuous_onI) simp
  have g_mono_aux: \<open>g x \<le>\<ge>\<^bsub>\<eta>\<^esub> g y\<close> if  \<open>x \<le> y\<close> for x y
    unfolding \<eta>_def using that by simp (smt (verit, best))
  have g_mono: \<open>monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) g\<close>
    by (intro monotoneI) (auto simp:dir_le_refl intro!:g_mono_aux)

  have a: \<open>map_pmf (\<lambda>\<omega>. s \<in> \<omega>) (subsample U) = bernoulli_pmf f\<close> if \<open>s \<in> U\<close> for s
  proof -
    have \<open>measure (pmf_of_set ?C) {x. s \<in> x} = real subsample_size / card U\<close>
      by (intro n_subsets_prob subssample_size_le_card_U that assms(1))
    also have \<open>\<dots> = f\<close> unfolding f_def assms(2) by simp
    finally have \<open>measure (pmf_of_set ?C) {x. s \<in> x} = f\<close> by simp
    thus ?thesis by (intro eq_bernoulli_pmfI) (simp add: pmf_map vimage_def subsample_def)
  qed

  have \<open>?L \<le> (\<Prod>s\<in>S. (\<integral>\<omega>. g (s \<in> \<omega>) \<partial>subsample U))\<close>
    by (intro na_imp_prod_mono[OF _ g_mono] g_borel assms(4)) auto
  also have \<open>\<dots> = (\<Prod>s\<in>S. (\<integral>\<omega>. g \<omega> \<partial>map_pmf (\<lambda>\<omega>. s \<in> \<omega>) (subsample U)))\<close> by simp
  also have \<open>\<dots> = ?R\<close> using a assms(3) by (intro prod.cong refl) (metis in_mono)
  finally show ?thesis .
qed

(* Copied as-is for Lemma 2 *)
context
  fixes \<phi> :: \<open>real \<Rightarrow> bool \<Rightarrow> real\<close>
  assumes phi :
    \<open>\<And> x b. \<lbrakk>0 < x; x \<le> 1\<rbrakk> \<Longrightarrow> \<phi> x b \<ge> 0\<close>
    \<open>\<And> p x.
      \<lbrakk>0 < p; p \<le> 1; 0 < x; x \<le> 1\<rbrakk> \<Longrightarrow>
      measure_pmf.expectation (bernoulli_pmf p) (\<phi> x) \<le> \<phi> (x / p) True\<close>
    \<open>\<And> x y.
      \<lbrakk>0 < x; x \<le> y; y \<le> 1\<rbrakk> \<Longrightarrow>
      \<phi> x False \<le> \<phi> y False\<close>
begin

private abbreviation (input)
  \<open>aux \<equiv> \<lambda> S state. (\<Prod> x \<in> S. \<phi> (f ^ state_k state) (x \<in> state_chi state))\<close>

lemma run_steps_preserves_expectation_le:
  fixes \<sigma> :: "'a run_state"
  assumes \<open>S \<subseteq> run_state_set \<sigma>\<close>
  shows \<open>measure_pmf.expectation (run_state_pmf \<sigma>) (aux S) \<le> \<phi> 1 True ^ card S\<close>
  using assms
proof (induction \<sigma> arbitrary: S rule: run_state_induct)
  case 1 thus ?case by simp
next
  case (2 xs x)

  have \<open>finite (set_pmf (run_steps xs))\<close>
    using finite_run_state_pmf[where \<sigma>=\<open>FinalState xs\<close>] by simp
  note [simp] = integrable_measure_pmf_finite[OF this]

  have fin_S: "finite S" using finite_run_state_set 2(2) finite_subset by auto

  have b: "aux S \<omega> = aux (S - {x}) \<omega> * aux (S \<inter> {x}) \<omega>" for \<omega> :: "'a state"
    using fin_S by (subst prod.union_disjoint[symmetric]) (auto intro:prod.cong)

  have c: "finite (set_pmf (run_steps xs \<bind> step_1 x))"
    using finite_run_state_pmf[where \<sigma> ="IntermState xs x"] by simp

  have d:"(\<integral>u. aux (S\<inter>{x}) u \<partial>step_1 x \<tau>) \<le> \<phi> 1 True^(card (S \<inter> {x}))"  (is "?L \<le> ?R")
    if "\<tau> \<in> set_pmf (run_steps xs)" for \<tau> 
  proof(cases "x \<in> S")
    case True
    hence "?L = measure_pmf.expectation (bernoulli_pmf (f ^ state_k \<tau>)) (\<lambda>x. \<phi> (f ^ state_k \<tau>) x)"
      unfolding step_1_def Let_def map_pmf_def[symmetric] integral_map_pmf
      by (intro integral_cong_AE AE_pmfI) simp_all
    also have "\<dots> \<le> \<phi> (f ^ state_k \<tau> / f ^ state_k \<tau>) True"
      using f f_le_1 by (intro phi(2) power_le_one zero_less_power) auto
    also have "\<dots> \<le> \<phi> 1 True" using f by (simp add:divide_simps)
    also have "\<dots> = \<phi> 1 True ^ card (S \<inter> {x})" using True by simp
    finally show ?thesis by simp
  next 
    case False thus ?thesis by simp
  qed

  have "(\<integral>\<tau>. aux S \<tau> \<partial>(bind_pmf (run_steps xs) (step_1 x))) = 
    (\<integral>\<tau>. (\<integral>u. aux (S - {x}) \<tau> * aux (S \<inter> {x}) u \<partial>step_1 x \<tau>) \<partial>run_steps xs)"
    unfolding integral_bind_pmf[OF bounded_finite[OF c]] b
    by (intro integral_cong_AE AE_pmfI arg_cong2[where f="(*)"] prod.cong) (auto simp:step_1_def) 
  also have "\<dots> = (\<integral>\<tau>. aux (S-{x}) \<tau> * (\<integral>u. aux (S\<inter>{x}) u \<partial>step_1 x \<tau>) \<partial>run_steps xs)"
    by simp
  also have "\<dots> \<le> (\<integral>\<tau>. aux (S-{x}) \<tau> * (\<phi> 1 True)^ card (S\<inter>{x}) \<partial>run_steps xs)"
    using f f_le_1
    by (intro integral_mono_AE AE_pmfI mult_left_mono prod_nonneg phi(1) power_le_one d) auto
  also have "\<dots> = (\<phi> 1 True) ^ card (S\<inter>{x}) * (\<integral>\<tau>. aux (S-{x}) \<tau> \<partial>(run_state_pmf (FinalState xs)))"
    by simp
  also have "\<dots> \<le> (\<phi> 1 True) ^ card (S\<inter>{x}) * (\<phi> 1 True)^ card (S - {x})"
    using phi(1) 2(2) by (intro mult_left_mono 2(1)) auto
  also have "\<dots> = (\<phi> 1 True) ^ (card ((S\<inter>{x}) \<union> (S-{x})))"
    using fin_S by (subst card_Un_disjoint) (auto simp add:power_add)
  also have "\<dots> = (\<phi> 1 True) ^ card S" by (auto intro!:arg_cong2[where f="\<lambda>x y. x ^ (card y)"])
  finally show ?case by simp 
next
  case (3 xs x)
  define p where  \<open>p = run_state_pmf (IntermState xs x)\<close>
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = p \<bind> step_2\<close>
    by (simp add:run_steps_snoc p_def)

  have fin_S: "finite S" using finite_run_state_set 3(2) finite_subset by auto

  have \<open>finite (set_pmf p)\<close>
    using finite_run_state_pmf[where \<sigma>=\<open>IntermState xs x\<close>] by (simp add:p_def)
  note [simp] = integrable_measure_pmf_finite[OF this]

  have q:"finite (set_pmf (p \<bind> step_2))"
    using finite_run_state_pmf[where \<sigma>=\<open>FinalState (xs@[x])\<close>] b by simp

  have c: "(\<integral>u. (\<Prod>s\<in>S. \<phi> (f * f ^ state_k \<tau>) (s \<in> u)) \<partial>subsample (state_chi \<tau>)) \<le> aux S \<tau>"
    (is "?L \<le> ?R") if that': "\<tau> \<in> set_pmf p" "card(state_chi \<tau>) \<ge> threshold" for \<tau>
  proof -
    let ?q ="subsample (state_chi \<tau>)"
    let ?U = "state_chi \<tau>"

    define k' where "k' = state_k \<tau>+1"
    have "card (state_chi \<tau>) \<le> threshold" 
      using card_run_state_pmf[where \<sigma>="IntermState xs x"] that(1) 
      unfolding p_def AE_measure_pmf_iff by auto
    hence d:"card (state_chi \<tau>) = threshold" using that(2) by auto
    hence e:"finite (state_chi \<tau>)" using threshold_pos card_gt_0_iff by blast 

    have g: "y \<subseteq> state_chi \<tau>" if "y \<in> set_pmf (subsample (state_chi \<tau>))"  for y 
      using that subsample_finite_nonempty[OF that'(2)] unfolding subsample_def by auto

    have h: "f ^ k' \<in> {0<..1}" using f f_le_1 by (auto intro:power_le_one)
    have h2: "f ^ state_k \<tau> \<in> {0<..1}" using f f_le_1 by (auto intro:power_le_one)

    have "?L = (\<integral>u. (\<Prod>s\<in>(S-?U) \<union> (S\<inter>?U). \<phi> (f^k') (s\<in>u)) \<partial>?q)"
      unfolding k'_def using fin_S by (intro integral_cong_AE prod.cong AE_pmfI) auto 
    also have "\<dots> = (\<integral>u. (\<Prod>s\<in>(S-?U). \<phi> (f^k') (s\<in>u)) * (\<Prod>s\<in>(S\<inter>?U). \<phi> (f^k') (s\<in>u)) \<partial>?q)"
      using fin_S by (subst prod.union_disjoint) auto
    also have "\<dots> = (\<integral>u. (\<Prod>s\<in>(S-?U). \<phi> (f^k') False) * (\<Prod>s\<in>(S\<inter>?U). \<phi>(f^k') (s\<in>u)) \<partial>?q)"
      using g by (intro integral_cong_AE AE_pmfI arg_cong2[where f="(*)"] prod.cong 
          arg_cong2[where f="\<phi>"]) auto
    also have "\<dots> = (\<Prod>s\<in>(S-?U). \<phi> (f^k') False)*(\<integral>u. (\<Prod>s\<in>(S\<inter>?U). \<phi> (f^k') (s\<in>u)) \<partial>?q)"
      by simp
    also have "\<dots> \<le> (\<Prod>s\<in>(S-?U). \<phi> (f^k') False)*(\<Prod>s\<in>(S\<inter>?U). (\<integral>u. \<phi> (f^k') u \<partial>bernoulli_pmf f))"
      using h by (intro mult_left_mono int_prod_subsample_eq_prod_int[OF e d] prod_nonneg)
        (auto intro!:phi(1))
    also have "\<dots> \<le> (\<Prod>s\<in>(S-?U). \<phi> (f^k') False) * (\<Prod>s\<in>(S\<inter>?U). \<phi> (f^k'/f) True)"
      using h f f_le_1 
      by (intro mult_left_mono prod_mono phi(2) conjI integral_nonneg_AE AE_pmfI phi(1) prod_nonneg)
         auto
    also have "\<dots> \<le> (\<Prod>s\<in>(S-?U). \<phi> (f^state_k \<tau>) False) * (\<Prod>s\<in>(S\<inter>?U). \<phi> (f^state_k \<tau>) True)"
      unfolding k'_def
      using h h2 f f_le_1 by (intro mult_mono prod_mono conjI phi(1,3) prod_nonneg power_le_one)auto
    also have "\<dots> = (\<Prod>s\<in>(S-?U). \<phi>(f^state_k \<tau>) (s \<in> ?U))*(\<Prod>s\<in>(S\<inter>?U). \<phi>(f^state_k \<tau>) (s \<in> ?U))"
      by simp
    also have "\<dots> = (\<Prod>s\<in>(S-?U)\<union>(S\<inter>?U). \<phi>(f^state_k \<tau>) (s \<in> ?U))"
      using fin_S by (subst prod.union_disjoint[symmetric]) (auto)
    also have "\<dots> = aux S \<tau>" by (intro prod.cong) auto
    finally show ?thesis by simp
  qed

  have "(\<integral>\<tau>. aux S \<tau> \<partial>(run_state_pmf (FinalState (xs@[x])))) = (\<integral>\<tau>. aux S \<tau> \<partial>(bind_pmf p step_2))"
    unfolding b by simp
  also have "\<dots> = (\<integral>\<tau>. (\<integral>u. aux S u \<partial>step_2 \<tau>) \<partial>p)" by (intro integral_bind_pmf bounded_finite q)
  also have "\<dots> = (\<integral>\<tau>. (if card(state_chi \<tau>) < threshold then aux S \<tau> 
    else (\<integral>u. (\<Prod>s\<in>S. \<phi> (f * f ^ state_k \<tau>) (s \<in> u)) \<partial>(subsample (state_chi \<tau>)))) \<partial>p)"
    unfolding step_2_def Let_def by (simp add:if_distrib if_distribR cong:if_cong)
  also have "\<dots> \<le> (\<integral>\<tau>. (if card(state_chi \<tau>) < threshold then aux S \<tau> else aux S \<tau>)\<partial>p)"
    using c by (intro integral_mono_AE AE_pmfI) auto
  also have "\<dots> = (\<integral>\<tau>. aux S \<tau> \<partial>p)" by simp
  also have "\<dots> \<le> \<phi> 1 True ^ card S" using 3(2) unfolding p_def by (intro 3(1)) auto
  finally show ?case by simp
qed

end

context
  fixes q :: real and h :: \<open>real \<Rightarrow> real\<close>
  assumes h:
    \<open>0 < q\<close> \<open>q \<le> 1\<close> 
    \<open>concave_on {0 .. 1 / q} h\<close> 
    \<open>\<And> x. \<lbrakk>0 \<le> x; x * q \<le> 1\<rbrakk> \<Longrightarrow> h x \<ge> 0\<close>
begin

private abbreviation (input)
  \<open>aux' \<equiv> \<lambda>S \<sigma>. (\<Prod>x \<in> S. of_bool (state_p \<sigma> \<ge> q) * h (of_bool (x \<in> state_chi \<sigma>) / state_p \<sigma>))\<close>

(* Lemma 3 *)
lemma run_steps_preserves_expectation_le' :
  assumes \<open>S \<subseteq> run_state_set \<sigma>\<close>
  shows \<open>(\<integral>\<tau>. aux' S \<tau> \<partial> (run_state_pmf \<sigma>)) \<le> (h 1) ^ card S\<close> (is "?L \<le> ?R")
proof -
  define \<phi> where "\<phi> = (\<lambda>p e. of_bool (q \<le> p) * h(of_bool e / p))"
  have \<phi>_1: "\<phi> x b \<ge> 0" if "x > 0" "x \<le> 1" for x b
    using h(1,4) that unfolding \<phi>_def by simp 
  have \<phi>_2: "\<phi> x True * p + \<phi> x False * (1 - p) \<le> \<phi> (x / p) True" if "x \<in> {0<..1}" "p \<in> {0<..1}" 
    for x p
  proof (cases " 1 / x \<in> {0..1 / q}")
    case True
    hence a:"q \<le> x" using that(1) h(1) by (simp add:divide_simps) 
    also have "\<dots> \<le> x/p" using that by (auto simp add:divide_simps) 
    finally have b:"q \<le> x / p" by simp
    show ?thesis
      unfolding \<phi>_def using that concave_onD[OF h(3) _ _ _ True, where t="p" and x="0"] a b h(1)
      by (auto simp:algebra_simps) 
  next
    case False
    hence a:"q > x" using that h(1) by (auto simp add:divide_simps)
    hence "q \<le> x/p \<Longrightarrow> 0 \<le> h (p / x)" using that by (intro h(4)) (auto simp:field_simps)
    thus ?thesis using a by (simp add:\<phi>_def)
  qed
  have \<phi>_3: "\<phi> x False \<le> \<phi> y False" if "x \<le> y" for x y
     using that by (auto intro:h(4) simp add:\<phi>_def) 

  have "?L = (\<integral>\<tau>. (\<Prod>x\<in>S. \<phi> (f ^ state_k \<tau>) (x \<in> state_chi \<tau>)) \<partial>(run_state_pmf \<sigma>))"
    unfolding \<phi>_def by (simp add:state_p_def)
  also have "\<dots> \<le> \<phi> 1 True^ card S" using \<phi>_1 \<phi>_2 \<phi>_3
    by (intro run_steps_preserves_expectation_le assms ) auto
  also have "\<dots> = h 1 ^ card S" using h unfolding \<phi>_def by simp
  finally show ?thesis by simp
qed

end

text \<open>Analysis of the case where @{term "card (set xs) \<ge> threshold"}:\<close>

context
  fixes xs :: \<open>'a list\<close>
  assumes set_larger_than_threshold: \<open>card (set xs) \<ge> threshold\<close>
begin

definition \<open>q = real threshold / (4 * card (set xs))\<close>

lemma q_range: \<open>q \<in> {0<..1/4}\<close>
  using set_larger_than_threshold threshold_pos unfolding q_def by auto

(* Lemma 4 *)
lemma upper_tail_bound:
  assumes \<open>\<epsilon> \<in> {0<..1::real}\<close>
  assumes \<open>run_state_set \<sigma> \<subseteq> set xs\<close>
  shows \<open>measure (run_state_pmf \<sigma>)
    {\<omega>. real (card (state_chi \<omega>)) / state_p \<omega> \<ge> (1 + \<epsilon>) * card (set xs) \<and> state_p \<omega> \<ge> q}
    \<le> exp(-real threshold/12 * \<epsilon>^2)\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  let ?p = \<open>run_state_pmf \<sigma>\<close>
  define t where \<open>t = q * ln (1+\<epsilon>)\<close>
  define h where \<open>h x = 1 + q * x * (exp (t / q) - 1)\<close> for x

  let ?A' = \<open>run_state_set \<sigma>\<close>
  note [simp] = integrable_measure_pmf_finite[OF finite_run_state_pmf]

  let ?\<chi> = \<open>\<lambda>\<omega>. real (card (state_chi \<omega>))\<close>
  let ?X = \<open>\<lambda>i \<omega>. of_bool(i \<in> state_chi \<omega>)/state_p \<omega>\<close>
  let ?c = \<open>real (card (set xs))\<close>

  have t_gt_0: \<open>t > 0\<close> unfolding t_def using q_range assms(1) by auto

  have mono_exp_t: \<open>strict_mono (\<lambda>(x::real). exp (t * x))\<close>
    using t_gt_0 by (intro strict_monoI) auto

  have h_1_eq: \<open>h 1 = 1 + q * \<epsilon>\<close> using assms(1) unfolding h_def t_def by simp
  have h_1_pos: \<open>h 1 \<ge> 1\<close> unfolding h_1_eq using q_range assms(1) by auto

  define f where \<open>f x = - q * x\<^sup>2 / 3 - ln (1 + q * x) + q * ln (1 + x) * (1 + x)\<close> for x
  define f' where \<open>f' x = -2*x*q/3 - q/(1+q*x) + q*ln(1+x) + q\<close> for x

  have f_deriv: \<open>(f has_real_derivative (f' x)) (at x)\<close> if \<open>x \<ge> 0\<close> \<open>x \<le> 1\<close> for x
  proof -
    have \<open>0 < (1::real) + 0\<close> by simp
    also have \<open>\<dots> \<le> 1 + q * x\<close> using that q_range by (intro add_mono mult_nonneg_nonneg) auto
    finally have \<open>0 < 1 + q * x\<close> by simp
    thus ?thesis
      using that q_range unfolding f_def f'_def power2_eq_square
      by (auto intro!:derivative_eq_intros)
  qed

  have f_deriv_nonneg: \<open>f' x \<ge> 0\<close> if \<open>x \<ge> 0\<close> \<open>x \<le> 1\<close> for x
  proof -
    have \<open>exp(2*x/3) = exp((1-x)*\<^sub>R 0 + x *\<^sub>R (2/3))\<close> by simp
    also have \<open>\<dots> \<le> (1-x)*exp 0 + x*exp(2/3)\<close> by (intro that convex_onD[OF exp_convex]) auto
    also have \<open>\<dots> = 1 + x*(exp (2/3)-exp 0)\<close> by (simp add:algebra_simps)
    also have \<open>\<dots> \<le> 1+ x* 1\<close> by (intro add_mono order.refl mult_left_mono that) (approximation 5)
    finally have \<open>exp(2*x/3) \<le> exp(ln(1+x))\<close> using that by simp
    hence \<open>0 \<le> ln(1+x) - 2*x/3\<close> by simp
    also have \<open>\<dots> = ln(1+x) +1 -2*x/3 - 1\<close> by simp
    also have \<open>\<dots> \<le> ln(1+x) +1 -2 * x/3 - 1/(1+q*x)\<close>
      using q_range that by (intro add_mono diff_mono) (auto simp:divide_simps)
    finally have b: \<open>0 \<le> ln(1+x) +1 -2 * x/3 - 1/(1+q*x)\<close> by simp

    have \<open>f' x = q * (-2 * x/3 - 1/(1+q*x) +ln(1+x) +1)\<close>
      unfolding f'_def by (simp add:algebra_simps)
    also have \<open>\<dots> \<ge> 0\<close>  using b q_range by (intro mult_nonneg_nonneg) auto
    finally show ?thesis by simp
  qed

  have f_mono: \<open>f x \<le> f y\<close> if \<open>x \<le> y\<close> \<open>x \<ge> 0\<close> \<open>y \<le> 1\<close> for x y
    using f_deriv f_deriv_nonneg order_trans[OF _ that(3)] order_trans[OF that(2)]
    by (intro DERIV_nonneg_imp_nondecreasing[OF that(1)]) blast

  have f_nonneg: \<open>f x \<ge> 0\<close> if \<open>x \<in> {0<..1}\<close> for x
  proof -
    have \<open>0 = f 0\<close> unfolding f_def by simp
    also have \<open>\<dots> \<le> f x\<close> using that by (intro f_mono)  auto
    finally show ?thesis by simp
  qed

  have a: \<open>ln (h 1) - t * (1 + \<epsilon>) \<le> - q * \<epsilon>^2 / 3\<close>
    unfolding h_1_eq t_def using f_nonneg[OF assms(1)] unfolding f_def by (simp add:algebra_simps)

  have b: \<open>exp (t / y) \<le> h (1 / y)\<close> if \<open>y \<ge> q\<close> for y
  proof -
    have \<open>exp (t / y) = exp ((1-q/y) *\<^sub>R 0 + (q/y) *\<^sub>R (t/q))\<close> using q_range by simp
    also have \<open>\<dots> \<le> (1-q/y) * exp 0 + (q/y) * exp (t/q)\<close> using that q_range
      by (intro convex_onD[OF exp_convex]) simp_all
    also have \<open>\<dots> = h (1 / y)\<close> unfolding h_def by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have c: \<open>1 \<le> h 0\<close> unfolding h_def by simp

  have h_concave: \<open>concave_on {0..1 / q} h\<close>
    unfolding h_def by (intro concave_on_linorderI) (auto simp:algebra_simps)

  have h_nonneg: \<open>h y \<ge> 0\<close> if \<open>y \<in> {0..1/q}\<close> for y
  proof -
    have \<open>0 \<le> (1-q*y) + q*y * 0\<close> using that q_range by (auto simp:field_simps)
    also have \<open>\<dots> \<le> (1-q*y) + q*y*exp(t/q)\<close> using that q_range
      by (intro add_mono mult_left_mono mult_nonneg_nonneg) auto
    also have \<open>\<dots> = h y\<close> unfolding h_def by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have \<open>?L = measure ?p {\<omega>. exp (t*(?\<chi> \<omega>/state_p \<omega>)) \<ge> exp (t*((1+\<epsilon>)* ?c))\<and>state_p \<omega>\<ge> q}\<close>
    by (subst strict_mono_less_eq[OF mono_exp_t]) simp
  also have \<open>\<dots> \<le> \<P>(\<omega> in ?p. of_bool(state_p \<omega> \<ge> q)*exp (t*(?\<chi> \<omega>/state_p \<omega>))\<ge> exp (t*((1+\<epsilon>)*?c)))\<close>
    by (intro pmf_mono) auto
  also have \<open>\<dots> \<le> (\<integral>\<omega>. of_bool(state_p \<omega> \<ge> q)* exp (t*(?\<chi> \<omega>/state_p \<omega>))\<partial>?p) / exp (t*((1+\<epsilon>)*?c))\<close>
    by (intro integral_Markov_inequality_measure[where A=\<open>{}\<close>]) simp_all
  also have \<open>\<dots> = (\<integral>\<omega>. of_bool(state_p \<omega> \<ge> q) * exp((\<Sum>i\<in>?A'. t * ?X i \<omega>)) \<partial>?p)/exp(t*((1+\<epsilon>)*?c))\<close>
    using state_chi_run_state_pmf[where \<sigma>=\<open>\<sigma>\<close>] Int_absorb1
    unfolding sum_divide_distrib[symmetric] sum_distrib_left[symmetric]
    by (intro integral_cong_AE arg_cong2[where f=\<open>(/)\<close>])
      (auto simp:AE_measure_pmf_iff intro!:arg_cong[where f=\<open>card\<close>])
  also have \<open>\<dots> \<le> (\<integral>\<omega>. (\<Prod>i \<in> ?A'. of_bool(state_p \<omega> \<ge> q)*exp( t* ?X i \<omega>)) \<partial>?p)/ exp(t*((1+\<epsilon>)*?c))\<close>
    unfolding exp_sum[OF finite_run_state_set] prod.distrib
    by (intro divide_right_mono integral_mono_AE AE_pmfI)
      (auto intro!:mult_nonneg_nonneg prod_nonneg)
  also have \<open>\<dots> \<le> (\<integral>\<omega>. (\<Prod>i \<in> ?A'. of_bool(state_p \<omega> \<ge> q)*h( ?X i \<omega>)) \<partial>?p)/ exp (t*((1+\<epsilon>)*?c))\<close>
    using b c by (intro divide_right_mono integral_mono_AE AE_pmfI) (auto intro!:prod_mono)
  also have \<open>\<dots> \<le> h 1 ^ card ?A' / exp (t * ((1+\<epsilon>)* ?c))\<close>
    using q_range h_concave
    by (intro divide_right_mono run_steps_preserves_expectation_le')
      (auto intro!:h_nonneg simp:field_simps)
  also have \<open>\<dots> \<le> h 1 powr ?c / exp (t * ((1+\<epsilon>)* ?c))\<close>
    using card_mono[OF _ assms(2)] h_1_pos
    by (subst powr_realpow) (auto intro!:power_increasing divide_right_mono)
  also have \<open>\<dots> = exp (?c * (ln (h 1) - t * (1 + \<epsilon>)))\<close>
    using h_1_pos unfolding powr_def by (simp add:algebra_simps exp_diff)
  also have \<open>\<dots> \<le> exp (?c * (-q * \<epsilon>^2/3))\<close>
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono a) simp
  also have \<open>\<dots> = ?R\<close> using set_larger_than_threshold threshold_pos  unfolding q_def by auto
  finally show ?thesis by simp
qed

(* Lemma 5 *)
lemma q_bound:
  \<open>measure (run_steps xs) {\<omega>. state_p \<omega> < q} \<le> real (length xs) * exp(- real threshold/12)\<close>
proof -
  define \<sigma> where \<open>\<sigma> = FinalState xs\<close>

  define j where \<open>j = nat \<lfloor>log f q\<rfloor>\<close>

  have f_range: \<open>f \<ge> 0\<close> \<open>f \<le> 1\<close> using f f_le_1 by auto

  have \<open>q = f powr (log f q)\<close>
    using f f_lt_1 q_range by (intro powr_log_cancel[symmetric]) auto
  also have \<open>\<dots> \<le> f powr (\<lfloor>log f q\<rfloor>)\<close> by (intro powr_mono' f_range) simp
  also have \<open>\<dots> \<le> f powr (real (nat \<lfloor>log f q\<rfloor>))\<close> using f f_lt_1 q_range
    by (subst of_nat_int_floor) (auto intro:divide_nonpos_neg simp add:log_def)
  also have \<open>\<dots> = f ^ j\<close> using f unfolding j_def by (subst powr_realpow) auto
  finally have f_1: \<open>q \<le> f^j\<close> by simp

  have \<open>f^(j+1) = f powr (real (nat \<lfloor>log f q\<rfloor>+1))\<close>
    unfolding j_def using f by (subst powr_realpow) auto
  also have \<open>\<dots> \<le> f powr (log f q)\<close> by (intro powr_mono' f_range) linarith
  also have \<open>\<dots> = q\<close> using f f_lt_1 q_range by (intro powr_log_cancel) auto
  finally have f_2: \<open>f^(j+1) \<le> q\<close> by simp

  have \<open>2 * real (card (set xs)) * f^j \<le> 4*f* real (card (set xs)) * f^j\<close>
    using f f_le_1 by (intro mult_right_mono) auto
  also have \<open>\<dots> = 4 * real (card (set xs)) * f^(j+1)\<close> by simp
  also have \<open>\<dots> \<le> 4 * real (card (set xs)) * q\<close> using f_2 by (intro mult_left_mono) auto
  also have \<open>\<dots> = threshold\<close> using threshold_pos set_larger_than_threshold unfolding q_def by auto
  finally have f_3: \<open>2 * real (card (set xs)) * f^j \<le> threshold\<close> by simp

  have ih: \<open>run_state_set \<sigma> \<subseteq> set xs\<close> unfolding \<sigma>_def by simp

  have \<open>n > j\<close> if \<open>f^n < q\<close> for n
    unfolding not_le[symmetric] using that f_1 f_le_1 power_decreasing[OF _ f_range] by force
  hence \<open>measure (run_steps xs) {\<omega>. state_p \<omega> < q} \<le> measure (run_state_pmf \<sigma>) {\<omega>. state_k \<omega> > j}\<close>
    unfolding \<sigma>_def run_state_pmf.simps by (intro pmf_mono) (auto simp:state_p_def)
  also have \<open>\<dots> \<le> real (len_run_state \<sigma>) * exp(- real threshold/12)\<close>
    using ih
  proof (induction \<sigma> rule:run_state_induct)
    case 1
    then show ?case using q_range by (simp add:run_steps_def state_p_def initial_state_def)
  next
    case (2 ys x)
    have \<open>measure (step_1 x s) {\<omega>. state_k \<omega> > j} = indicator {\<omega>. state_k \<omega> > j} s\<close>
      for s :: \<open>'a state\<close>
      by (simp add:step_1_def map_pmf_def[symmetric])

    thus ?case using 2 by (simp add:measure_bind_pmf)
  next
    case (3 ys x)
    define p where \<open>p = run_state_pmf (IntermState ys x)\<close>

    have \<open>finite (set_pmf p)\<close> unfolding p_def by (intro finite_run_state_pmf)
    note [simp] = integrable_measure_pmf_finite[OF this]

    have b: \<open>run_state_pmf (FinalState (ys@[x])) = p \<bind> step_2\<close>
      by (simp add:run_steps_snoc p_def)

    have d: \<open>run_state_set (IntermState ys x) \<subseteq> set xs\<close>
      using 3(2) by simp

    have a':\<open>measure (step_2 s) {\<omega>. state_k \<omega> > j} \<le>
      indicator {\<omega>. state_k \<omega> > j \<or> card (state_chi \<omega>) \<ge> threshold \<and> state_k \<omega> = j} s\<close>
      for j and s :: \<open>'a state\<close>
      by (simp add:step_2_def Let_def indicator_def)

    have a:\<open>measure (step_2 s) {\<omega>. state_p \<omega> < q} \<le>
      indicator {\<omega>. state_p \<omega> < q \<or> card (state_chi \<omega>) \<ge> threshold} s\<close>
      for s :: \<open>'a state\<close>
      by (simp add:step_2_def Let_def indicator_def)

    have \<open>measure p {\<omega>. card (state_chi \<omega>) \<ge> threshold \<and> state_k \<omega> = j} \<le>
      measure p {\<omega>. (1+1) * real(card(set xs)) \<le> real(card(state_chi \<omega>))/state_p \<omega> \<and> q\<le>state_p \<omega>}\<close>
      using f_1 f_3 f by (intro pmf_mono) (simp add:state_p_def field_simps)
    also have \<open>\<dots> \<le> exp (- real threshold / 12 * 1^2)\<close>
      unfolding p_def by (intro upper_tail_bound d) simp
    finally have c:
      \<open>measure p {\<omega>. card (state_chi \<omega>) \<ge> threshold \<and> state_k \<omega> = j} \<le> exp (- real threshold / 12)\<close>
      by simp

    have \<open>measure (run_state_pmf (FinalState (ys @ [x]))) {\<omega>. state_k \<omega> > j} =
      (\<integral>s. measure (step_2 s) {\<omega>. state_k \<omega> > j} \<partial>p)\<close>
      unfolding b by (simp add:measure_bind_pmf)
    also have \<open>\<dots> \<le> (\<integral>s. indicator {\<omega>. state_k \<omega>>j\<or>card(state_chi \<omega>)\<ge>threshold\<and>state_k \<omega>=j} s \<partial>p)\<close>
      by (intro integral_mono_AE AE_pmfI a') simp_all
    also have \<open>\<dots> = measure p {\<omega>. state_k \<omega> > j \<or> card (state_chi \<omega>) \<ge> threshold \<and> state_k \<omega> = j}\<close>
      by simp
    also have \<open>\<dots> \<le>
      measure p {\<omega>. state_k \<omega> > j} +
      measure p {\<omega>. card (state_chi \<omega>) \<ge> threshold \<and> state_k \<omega> = j}\<close>
      by (intro pmf_add) auto
    also have \<open>\<dots> \<le> length ys * exp (- real threshold / 12) + exp (- real threshold / 12)\<close>
      using 3(1)[OF d] by (intro add_mono c) (simp add:p_def)
    also have \<open>\<dots> = real (len_run_state (FinalState (ys @ [x]))) * exp (- real threshold / 12)\<close>
      by (simp add:algebra_simps)
    finally show ?case by simp
  qed
  also have \<open>\<dots> = real (length xs) * exp(- real threshold/12)\<close> by (simp add:\<sigma>_def)
  finally show ?thesis by simp
qed

(* Lemma 6 *)
lemma lower_tail_bound:
  assumes \<open>\<epsilon> \<in> {0<..<1::real}\<close>
  shows \<open>measure (run_steps xs)
    {\<omega>. real (card (state_chi \<omega>)) / state_p \<omega> \<le> (1 - \<epsilon>) * card (set xs) \<and> state_p \<omega> \<ge> q}
    \<le> exp(-real threshold/8 * \<epsilon>^2)\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  let ?p = \<open>run_state_pmf (FinalState xs)\<close>
  define t where \<open>t = q * ln (1-\<epsilon>)\<close>
  define h where \<open>h x = 1 + q * x * (exp (t / q) - 1)\<close> for x

  let ?A' = \<open>set xs\<close>
  have \<open>finite (set_pmf (run_steps xs))\<close>
    using finite_run_state_pmf[where \<sigma>=\<open>FinalState xs\<close>] by simp
  note [simp] = integrable_measure_pmf_finite[OF this]

  let ?\<chi> = \<open>\<lambda>\<omega>. real (card (state_chi \<omega>))\<close>
  let ?X = \<open>\<lambda>i \<omega>. of_bool(i \<in> state_chi \<omega>)/state_p \<omega>\<close>
  let ?c = \<open>real (card (set xs))\<close>

  have t_lt_0: \<open>t < 0\<close>
    unfolding t_def using q_range assms(1) by (intro mult_pos_neg ln_less_zero) auto

  have mono_exp_t: \<open>exp (t * x) \<le> exp (t * y) \<longleftrightarrow> y \<le> x\<close> for x y
    using t_lt_0 by auto

  have h_1_eq: \<open>h 1 = 1 - q * \<epsilon>\<close> using assms(1) unfolding h_def t_def by simp
  have \<open>\<epsilon> * (q * 4) \<le> 1 * 1\<close> using q_range assms(1) by (intro mult_mono) auto
  hence h_1_pos: \<open>h 1 \<ge> 3/4\<close> unfolding h_1_eq by (auto simp:algebra_simps)

  define f where \<open>f x = - q * x\<^sup>2 / 2 - ln (1 - q * x) + q * ln (1 - x) * (1 - x)\<close> for x
  define f' where \<open>f' x = -x*q + q/(1-q*x) - q*ln(1-x) - q\<close> for x

  have f_deriv: \<open>(f has_real_derivative (f' x)) (at x)\<close> if \<open>x \<ge> 0\<close> \<open>x < 1\<close> for x
  proof -
    have \<open>q * x \<le> (1/4) * 1\<close> using that q_range by (intro mult_mono) auto
    also have \<open>\<dots> < 1\<close> by simp
    finally have \<open>q * x < 1\<close> by simp
    thus ?thesis
      using that q_range unfolding f_def f'_def power2_eq_square
      by (auto intro!:derivative_eq_intros)
  qed

  have f_deriv_nonneg: \<open>f' x \<ge> 0\<close> if \<open>x \<ge> 0\<close> \<open>x < 1\<close> for x
  proof -
    have \<open>q * x \<le> (1/4) * 1\<close> using that q_range by (intro mult_mono) auto
    also have \<open>\<dots> < 1\<close> by simp
    finally have a:\<open>q * x < 1\<close> by simp

    have \<open>0 \<le> -ln(1-x) -x\<close> using ln_one_minus_pos_upper_bound[OF that] by simp
    also have \<open>\<dots> = -ln(1-x) -1 -x + 1\<close> by simp
    also have \<open>\<dots> \<le> -ln(1-x) -1 -x + 1/(1-q*x)\<close>
      using a q_range that by (intro add_mono diff_mono) (auto simp:divide_simps)
    finally have b: \<open>0 \<le> -ln(1-x) -1 - x + 1/(1-q*x)\<close> by simp

    have \<open>f' x = q * (-x + 1/(1-q*x) -ln(1-x) -1)\<close>
      unfolding f'_def by (simp add:algebra_simps)
    also have \<open>\<dots> \<ge> 0\<close>  using b q_range by (intro mult_nonneg_nonneg) auto
    finally show ?thesis by simp
  qed

  have f_mono: \<open>f x \<le> f y\<close> if \<open>x \<le> y\<close> \<open>x \<ge> 0\<close> \<open>y < 1\<close> for x y
    using f_deriv f_deriv_nonneg le_less_trans[OF _ that(3)] order_trans[OF that(2)]
    by (intro DERIV_nonneg_imp_nondecreasing[OF that(1)]) blast

  have f_nonneg: \<open>f x \<ge> 0\<close> if \<open>x \<in> {0<..<1}\<close> for x
  proof -
    have \<open>0 = f 0\<close> unfolding f_def by simp
    also have \<open>\<dots> \<le> f x\<close> using that by (intro f_mono)  auto
    finally show ?thesis by simp
  qed

  have a: \<open>ln (h 1) - t * (1 - \<epsilon>) \<le> - q * \<epsilon>^2 / 2\<close>
    unfolding h_1_eq t_def using f_nonneg[OF assms(1)] unfolding f_def
    by (simp add:divide_simps)

  have b: \<open>exp (t / y) \<le> h (1 / y)\<close> if \<open>y \<ge> q\<close> for y
  proof -
    have \<open>exp (t / y) = exp ((1-q/y) *\<^sub>R 0 + (q/y) *\<^sub>R (t/q))\<close> using q_range by simp
    also have \<open>\<dots> \<le> (1-q/y) * exp 0 + (q/y) * exp (t/q)\<close> using that q_range
      by (intro convex_onD[OF exp_convex]) simp_all
    also have \<open>\<dots> = h (1 / y)\<close> unfolding h_def by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have c: \<open>1 \<le> h 0\<close> unfolding h_def by simp

  have h_concave: \<open>concave_on {0..1 / q} h\<close>
    unfolding h_def by (intro concave_on_linorderI) (auto simp:algebra_simps)

  have h_nonneg: \<open>h y \<ge> 0\<close> if \<open>y \<in> {0..1/q}\<close> for y
  proof -
    have \<open>0 \<le> (1-q*y) + q*y * 0\<close> using that q_range by (auto simp:field_simps)
    also have \<open>\<dots> \<le> (1-q*y) + q*y*exp(t/q)\<close> using that q_range
      by (intro add_mono mult_left_mono mult_nonneg_nonneg) auto
    also have \<open>\<dots> = h y\<close> unfolding h_def by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have \<open>?L = measure ?p {\<omega>. exp (t*(?\<chi> \<omega>/state_p \<omega>)) \<ge> exp (t*((1-\<epsilon>)* ?c))\<and>state_p \<omega>\<ge> q}\<close>
    by (subst  mono_exp_t) simp
  also have \<open>\<dots> \<le> \<P>(\<omega> in ?p. of_bool(state_p \<omega> \<ge> q)*exp (t*(?\<chi> \<omega>/state_p \<omega>))\<ge> exp (t*((1-\<epsilon>)*?c)))\<close>
    by (intro pmf_mono) auto
  also have \<open>\<dots> \<le> (\<integral>\<omega>. of_bool(state_p \<omega> \<ge> q)* exp (t*(?\<chi> \<omega>/state_p \<omega>))\<partial>?p) / exp (t*((1-\<epsilon>)*?c))\<close>
    by (intro integral_Markov_inequality_measure[where A=\<open>{}\<close>]) simp_all
  also have \<open>\<dots> = (\<integral>\<omega>. of_bool(state_p \<omega> \<ge> q) * exp((\<Sum>i\<in>?A'. t * ?X i \<omega>)) \<partial>?p)/exp(t*((1-\<epsilon>)*?c))\<close>
    using state_chi_run_state_pmf[where \<sigma>=\<open>FinalState xs\<close>] Int_absorb1
    unfolding sum_divide_distrib[symmetric] sum_distrib_left[symmetric]
    by (intro integral_cong_AE arg_cong2[where f=\<open>(/)\<close>])
      (auto simp:AE_measure_pmf_iff intro!:arg_cong[where f=\<open>card\<close>])
  also have \<open>\<dots> \<le> (\<integral>\<omega>. (\<Prod>i \<in> ?A'. of_bool(state_p \<omega> \<ge> q)*exp( t* ?X i \<omega>)) \<partial>?p)/ exp(t*((1-\<epsilon>)*?c))\<close>
    unfolding exp_sum[OF finite_set] prod.distrib
    by (intro divide_right_mono integral_mono_AE AE_pmfI)
     (auto intro!:mult_nonneg_nonneg prod_nonneg)
  also have \<open>\<dots> \<le> (\<integral>\<omega>. (\<Prod>i \<in> ?A'. of_bool(state_p \<omega> \<ge> q)*h( ?X i \<omega>)) \<partial>?p)/ exp (t*((1-\<epsilon>)*?c))\<close>
    using b c by (intro divide_right_mono integral_mono_AE AE_pmfI) (auto intro!:prod_mono)
  also have \<open>\<dots> \<le> h 1 ^ card ?A' / exp (t * ((1-\<epsilon>)* ?c))\<close>
    using q_range h_concave
    by (intro divide_right_mono run_steps_preserves_expectation_le')
      (auto intro!:h_nonneg simp:field_simps)
  also have \<open>\<dots> \<le> h 1 powr ?c / exp (t * ((1-\<epsilon>)* ?c))\<close>
    using h_1_pos by (subst powr_realpow) (auto intro!:power_increasing divide_right_mono)
  also have \<open>\<dots> = exp (?c * (ln (h 1) - t * (1 - \<epsilon>)))\<close>
    using h_1_pos unfolding powr_def by (simp add:algebra_simps exp_add[symmetric] exp_diff)
  also have \<open>\<dots> \<le> exp (?c * (-q * \<epsilon>^2/2))\<close>
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono a) simp
  also have \<open>\<dots> = ?R\<close> using set_larger_than_threshold threshold_pos unfolding q_def by auto
  finally show ?thesis by simp
qed

lemma correctness_aux:
  fixes \<epsilon> \<delta> :: real
  assumes "\<epsilon> \<in> {0<..<1}" "\<delta> \<in> {0<..<1}"
  assumes "real threshold \<ge> 12/\<epsilon>^2 * ln (3*real (length xs) /\<delta>)"
  defines "R \<equiv> real (card (set xs))"
  shows "measure (run_steps xs) {\<omega>. \<bar>real (card (state_chi \<omega>))/state_p \<omega> - R\<bar> > \<epsilon>*R } \<le> \<delta>" 
    (is "?L \<le> ?R")
proof -
  let ?\<chi> = "\<lambda>\<omega>. real (card (state_chi \<omega>)) / state_p \<omega>"
  let ?pmf = "run_steps xs"
  let ?pmf' = "run_state_pmf (FinalState xs)"
  let ?p = "state_p" 
  let ?l = "real (length xs)"
  have l_gt_0: "length xs > 0" using set_larger_than_threshold threshold_pos by auto
  hence l_ge_1: "?l \<ge> 1"  by linarith

  have d:"ln (3*real (length xs) /\<delta>) = - ln (\<delta>/(3*?l))"
    using l_ge_1 assms(2) by (subst (1 2) ln_div) auto

  have "exp (- real threshold / 12 * 1) \<le> exp (- real threshold / 12 * \<epsilon>^2)"
    using assms(1) by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono_neg power_le_one) auto
  also have "\<dots> \<le>  \<delta> / (3*?l)"
    using assms(1-3) l_ge_1 unfolding d by (subst ln_ge_iff[symmetric]) (auto simp:divide_simps)
  finally have "exp (- real threshold / 12) \<le> \<delta> / (3*?l)" by simp
  hence a: "?l * exp (- real threshold / 12) \<le> \<delta> / 3" using l_gt_0 by (auto simp:field_simps) 

  have c: "exp(-real threshold/12 * \<epsilon>^2) \<le> \<delta> / (3*?l)"
    using assms(1-3) l_ge_1 unfolding d by (subst ln_ge_iff[symmetric]) (auto simp:divide_simps)
  also have "\<dots> \<le> \<delta>/3" 
    using assms(1-3) l_ge_1 by (intro divide_left_mono) auto
  finally have c: "exp(-real threshold/12 * \<epsilon>^2) \<le> \<delta> / 3" by simp

  have "exp(-real threshold/8 * \<epsilon>^2) \<le> exp(-real threshold/12 * \<epsilon>^2)"
    by (intro iffD2[OF exp_le_cancel_iff]) auto
  also have "\<dots> \<le> \<delta>/3" using c by simp
  finally have b: "exp(-real threshold/8 * \<epsilon>^2) \<le> \<delta> / 3" by simp

  have "?L \<le> measure ?pmf {\<omega>. \<bar>?\<chi> \<omega> - R\<bar> \<ge> \<epsilon>*R}"
    by (intro pmf_mono) auto
  also have "\<dots> \<le> measure ?pmf {\<omega>. \<bar>?\<chi> \<omega> - R\<bar> \<ge> \<epsilon>*R \<and> ?p \<omega> \<ge> q} +  measure ?pmf {\<omega>. ?p \<omega> < q}"
    by (intro pmf_add) auto
  also have "\<dots> \<le> measure ?pmf {\<omega>. (?\<chi> \<omega>\<le>(1-\<epsilon>)*R\<or>?\<chi> \<omega>\<ge>(1+\<epsilon>)*R)\<and>?p \<omega>\<ge>q}+?l*exp(-real threshold/12)"
    by (intro pmf_mono add_mono q_bound) (auto simp:abs_real_def algebra_simps split:if_split_asm)
  also have "\<dots> \<le> measure ?pmf {\<omega>. ?\<chi> \<omega>\<le>(1-\<epsilon>)*R\<and>?p \<omega>\<ge>q}+measure ?pmf' {\<omega>. ?\<chi> \<omega>\<ge>(1+\<epsilon>)*R\<and>?p \<omega>\<ge>q}+\<delta>/3"
    unfolding run_state_pmf.simps by (intro add_mono pmf_add a) auto
  also have "\<dots> \<le> exp(-real threshold/8 * \<epsilon>^2)+ exp(-real threshold/12 * \<epsilon>^2)+\<delta>/3"
    unfolding R_def using assms(1) by (intro upper_tail_bound add_mono lower_tail_bound) auto
  also have "\<dots> \<le> \<delta> / 3 +  \<delta> / 3 + \<delta> / 3" by (intro  add_mono b c) auto
  finally show ?thesis by simp
qed

end

lemma deterministic_phase:
  assumes "card (run_state_set \<sigma>) < threshold"
  shows "run_state_pmf \<sigma> = return_pmf \<lparr> state_k = 0, state_chi = run_state_set \<sigma> \<rparr>"
  using assms
proof (induction \<sigma> rule:run_state_induct)
  case 1 thus ?case by (simp add:run_steps_def initial_state_def)
next
  case (2 xs x)
  have "card (set xs) < threshold" using 2(2) by (simp add:card_insert_if) presburger 
  moreover have "bernoulli_pmf 1 = return_pmf True"
    by (intro pmf_eqI) (auto simp:bernoulli_pmf.rep_eq)
  ultimately show ?case using 2(1) by (simp add:step_1_def bind_return_pmf)
next
  case (3 xs x)
  let ?p = \<open>run_state_pmf (IntermState xs x)\<close>
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = ?p \<bind> step_2\<close>
    by (simp add:run_steps_snoc)
  have a:"card (run_state_set (IntermState xs x)) < threshold" using 3(2) by simp 
  show ?case
    using 3(2) unfolding b 3(1)[OF a] by (simp add:step_2_def bind_return_pmf Let_def)
qed

theorem correctness:
  fixes \<epsilon> \<delta> :: real
  assumes "\<epsilon> \<in> {0<..<1}" "\<delta> \<in> {0<..<1}"
  assumes "real threshold \<ge> 12/\<epsilon>^2 * ln (3*real (length xs) /\<delta>)"
  defines "R \<equiv> real (card (set xs))"
  shows "measure (run_steps xs) {\<omega>. \<bar>real (card (state_chi \<omega>))/state_p \<omega> - R\<bar> > \<epsilon>*R } \<le> \<delta>" 
proof (cases "card (set xs) \<ge> threshold")
  case True
  show ?thesis
    unfolding R_def by (intro correctness_aux True assms)
next
  case False
  hence "run_steps xs = return_pmf \<lparr> state_k = 0, state_chi = (set xs) \<rparr>"
    using deterministic_phase[where \<sigma>="FinalState xs"] by simp
  thus ?thesis using assms(1,2) by (simp add:indicator_def state_p_def R_def not_less)
qed

end (* end cvm_algo_proof *)

end (* end theory *)
