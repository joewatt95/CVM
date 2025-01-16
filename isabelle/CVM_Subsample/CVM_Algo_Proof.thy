theory CVM_Algo_Proof

imports
  Probabilistic_Prime_Tests.Generalized_Primality_Test
  Negative_Association.Negative_Association_Permutation_Distributions
  CVM_Subsample.CVM_Algo
begin

datatype 'a run_state = FinalState "'a list" | IntermState "'a list" "'a"

lemma run_state_induct:
  fixes result :: "'a run_state"
  assumes "P (FinalState [])"
  assumes "\<And>xs x. P (FinalState xs) \<Longrightarrow> P (IntermState xs x)"
  assumes "\<And>xs x. P (IntermState xs x) \<Longrightarrow> P (FinalState (xs@[x]))"
  shows "P result" 
proof -
  have "P (FinalState xs) \<and> P (IntermState xs x)" for xs x
    using assms by (induction xs rule:rev_induct) auto
  thus ?thesis by (cases result) auto
qed

locale cvm_algo_proof = cvm_algo +
  assumes
    f : \<open>1 / 2 \<le> f\<close> and
    subsample : \<open>subsample_size < threshold\<close>
begin

lemma threshold_pos : \<open>threshold > 0\<close> using subsample by simp
lemma f_le_1 : \<open>f \<le> 1\<close> using subsample by (simp add: f_def)

lemma run_steps_snoc: "run_steps (xs @[x]) = run_steps xs \<bind> step_1 x \<bind> step_2"
  unfolding run_steps_def foldM_pmf_snoc step_def by (simp add:bind_assoc_pmf)

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
  define \<eta> where \<open>\<eta> \<equiv> if g True \<ge> g False then Fwd else Rev\<close>

  note subsample_finite_nonempty = 
    subsample_finite_nonempty[OF eq_refl[OF assms(2)[symmetric]]]
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

  note [simp] = integrable_measure_pmf_finite[OF subsample_finite_nonempty(3)]

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
      \<lbrakk>0 < p; p < 1; 0 < x; x \<le> 1\<rbrakk> \<Longrightarrow>
      measure_pmf.expectation (bernoulli_pmf p) (\<phi> x) \<le> \<phi> (x / p) True\<close>
    \<open>\<And> x y.
      \<lbrakk>0 < x; x \<le> y; y \<le> 1\<rbrakk> \<Longrightarrow>
      \<phi> x False \<le> \<phi> y False\<close>
begin

private abbreviation (input)
  \<open>aux \<equiv> \<lambda> S state. (
    \<Prod> x \<in> S. \<phi> (f ^ state_k state) (x \<in> state_chi state))\<close>

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

lemma step_1_card_le_threshold :
  \<open>\<turnstile>pmf
    \<lbrakk>(\<lambda> state. card (state_chi state) < threshold)\<rbrakk>
    step_1 x
    \<lbrakk>(\<lambda> state. card (state_chi state) \<le> threshold)\<rbrakk>\<close>
  using threshold_pos
  apply (auto
    simp flip: map_pmf_def
    simp add: step_1_def Let_def map_bind_pmf map_pmf_comp Set.remove_def)
  apply (metis Suc_diff_1 card_insert_le_m1 le_simps(2) threshold_pos)
  by (meson basic_trans_rules(21) card_Diff1_le le_simps(1))

private method simps = (
  simp
    flip: map_pmf_def
    add: step_1_def pmf_expectation_bind power_le_one Let_def,
  simp add: integral_measure_pmf algebra_simps,
  intro sum.cong refl)

lemma step_1_preserves_expectation_le :
  assumes
    \<open>finite U\<close>
    \<open>\<And> S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation state (aux S)
      \<le> (\<phi> 1 True) ^ card S\<close>
    (is \<open>\<And> S. _ \<Longrightarrow> ?L' S \<le> _\<close>)
    \<open>S \<subseteq> insert x' U\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step_1 x') (aux S)
    \<le> (\<phi> 1 True) ^ card S\<close>
    (is \<open>?L \<le> _\<close>)
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

lemma step_2_card_lt_threshold :
  \<open>\<turnstile>pmf \<lbrakk>\<lblot>True\<rblot>\<rbrakk> step_2 \<lbrakk>(\<lambda> state. card (state_chi state) < threshold)\<rbrakk>\<close>
  apply (simp
    split: if_splits
    add: step_2_def subsample_def image_def not_less Let_def)
  apply (subst (asm) set_pmf_of_set)
  using subsample subsample_finite_nonempty by auto

lemma step_preserves_card_lt_threshold :
  \<open>\<turnstile>pmf
    \<lbrakk>(\<lambda> state. card (state_chi state) < threshold)\<rbrakk>
    step x
    \<lbrakk>(\<lambda> state. card (state_chi state) < threshold)\<rbrakk>\<close>
  using step_2_card_lt_threshold by (fastforce simp add: step_def)

lemma step_2_preserves_finite_support :
  \<open>finite <| set_pmf <| state \<bind> step_2\<close>
  using state_finite_support subsample_finite_nonempty
  by (auto simp add: step_2_def subsample_def Let_def not_less)

lemma step_2_preserves_expectation_le :
  assumes
    (* \<open>finite U\<close> \<open>S \<subseteq> U\<close> *)
    \<open>finite S\<close>
    \<open>AE state in state. card (state_chi state) \<le> threshold\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step_2) (aux S)
    \<le> measure_pmf.expectation state (aux S)\<close>
    (is \<open>?L \<le> ?R\<close>)
proof -
  from assms step_2_preserves_finite_support state_finite_support have
    \<open>?L = (
      \<Sum> s \<in> set_pmf state \<inter> {s. card (state_chi s) < threshold}.
       pmf state s * aux S s) + (
      \<Sum> s \<in> set_pmf state \<inter> {s. card (state_chi s) = threshold}.
       pmf state s *
       measure_pmf.expectation (subsample <| state_chi s)
        (\<lambda> chi. aux S \<lparr>state_k = state_k s + 1, state_chi = chi\<rparr>))\<close>
    (is \<open>_ = ?L' (\<lambda> _ :: (_, _) state_scheme. measure_pmf.expectation _ _)\<close>)
    by (auto
      intro!: sum.cong
      simp flip: Collect_neg_eq
      simp add:
        step_2_def pmf_expectation_bind integral_measure_pmf AE_measure_pmf_iff
        Let_def if_distrib if_distribR sum.If_cases not_less)

  also from state_finite_support subsample_finite_nonempty
  have \<open>\<dots> \<le> ?R\<close>
    apply (simp add: integral_measure_pmf)
    sorry

  finally show ?thesis .
qed

end

fun run_state_pmf where
  "run_state_pmf (FinalState xs) = run_steps xs" |
  "run_state_pmf (IntermState xs x) = run_steps xs \<bind> step_1 x"

fun run_state_set where
  "run_state_set (FinalState xs) = set xs" |
  "run_state_set (IntermState xs x) = set xs \<union> {x}"

fun max_card_state where
  "max_card_state (FinalState _) = threshold - 1" |
  "max_card_state (IntermState _ _) = threshold"

lemma finite_run_state_set[simp]: "finite (run_state_set \<sigma>)" by (cases \<sigma>) auto

lemma finite_run_state_pmf: "finite (set_pmf (run_state_pmf \<sigma>))" 
proof (induction \<sigma> rule:run_state_induct)
  case 1 thus ?case by (simp add:run_steps_def)
next
  case (2 xs x) thus ?case by (simp add:step_1_def)
next
  case (3 xs x)
  have a: "run_state_pmf (FinalState (xs@[x])) = run_state_pmf (IntermState xs x) \<bind> step_2"
    by (simp add:run_steps_snoc)
  show ?case unfolding a using step_2_preserves_finite_support[OF 3] by simp
qed

lemma card_run_state_pmf:
  fixes \<sigma> :: "'a run_state"
  shows "AE \<omega> in run_state_pmf \<sigma>. card (state_chi \<omega>) \<le> max_card_state \<sigma>" 
proof (induction \<sigma> rule:run_state_induct)
  case 1
  then show ?case by (simp add:AE_measure_pmf_iff run_steps_def initial_state_def)
next
  case (2 xs x)
  have "card (insert x S) \<le> threshold \<and> card (Set.remove x S) \<le> threshold"
    if "card S \<le> threshold - 1" for S using threshold_pos that 
    by (metis card_Diff1_le diff_le_self order.trans remove_def card_insert_le_m1)
  thus ?case using 2 by (auto simp add:AE_measure_pmf_iff step_1_def)
next
  case (3 xs x)
  let ?p = \<open>run_state_pmf (IntermState xs x)\<close>
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = ?p \<bind> step_2\<close>
    by (simp add:run_steps_snoc)

  have "AE \<omega> in subsample U. card \<omega> = subsample_size" if "\<not>card U < threshold" for  U :: "'a set"
  proof -
    have "card U \<ge> threshold" using that by simp
    from subsample_finite_nonempty[OF this]
    show ?thesis unfolding subsample_def by (auto simp:AE_measure_pmf_iff)
  qed
  moreover have "subsample_size \<le> threshold - 1" 
    using threshold_pos subsample by simp
  ultimately show ?case 
    unfolding b AE_measure_pmf_iff set_bind_pmf by (auto simp: step_2_def Let_def)
qed

lemma run_steps_preserves_expectation_le :
  assumes
    \<open>S \<subseteq> run_state_set \<sigma>\<close>
  shows
    \<open>measure_pmf.expectation (run_state_pmf \<sigma>) (aux S) \<le> \<phi> 1 True ^ card S\<close>
  using assms
proof (induction \<sigma> arbitrary: S rule: run_state_induct)
  case 1 thus ?case by simp
next
  case (2 xs x)
  have a: \<open>finite (run_state_set (FinalState xs))\<close> by simp
  have "finite (set_pmf (run_steps xs))"
    using finite_run_state_pmf[where \<sigma>="FinalState xs"] by simp
  thus ?case using 2 unfolding run_state_pmf.simps
    by (intro step_1_preserves_expectation_le[OF _ a]) auto
next
  case (3 xs x)
  let ?p = \<open>run_state_pmf (IntermState xs x)\<close>
  have c: \<open>AE state in ?p. card (state_chi state) \<le> threshold\<close>
    using card_run_state_pmf[where \<sigma>="IntermState xs x"] by simp
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = ?p \<bind> step_2\<close>
    by (simp add:run_steps_snoc)
  have a: \<open>S \<subseteq> run_state_set (IntermState xs x)\<close> using 3(2) by auto
  have fin_S: \<open>finite S\<close> using a finite_run_state_set finite_subset by auto 
  show ?case unfolding b 
    using step_2_preserves_expectation_le[OF finite_run_state_pmf fin_S c] 3(1)[OF a] by simp
qed

end

context
  fixes q :: real and h :: \<open>real \<Rightarrow> real\<close>
  assumes
    \<open>0 < q\<close> \<open>q \<le> 1\<close> and
    \<open>concave_on {0 .. 1 / q} h\<close> and
    \<open>\<And> x. \<lbrakk>1 \<le> x; x * q \<le> 1\<rbrakk> \<Longrightarrow> h x \<ge> 0\<close>
begin

private abbreviation (input)
  \<open>aux' \<equiv> \<lambda> S x state. (
    let p = f ^ (state_k state)
    in \<Prod> x \<in> S. of_bool (p > q) * h ((1 / p) * indicat_real (state_chi state) x))\<close>

(* Lemma 3 *)
lemma run_steps_preserves_expectation_le' :
  assumes \<open>S \<subseteq> set xs\<close>
  shows
    \<open>measure_pmf.expectation (run_steps xs) (aux' S x) \<le> (h 1) ^ card S\<close>
proof -
  show ?thesis sorry
qed

end




end (* end cvm_algo_proof *)

end (* end theory *)
