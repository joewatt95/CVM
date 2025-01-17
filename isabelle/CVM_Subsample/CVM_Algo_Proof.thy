theory CVM_Algo_Proof

imports
  Probabilistic_Prime_Tests.Generalized_Primality_Test
  Negative_Association.Negative_Association_Permutation_Distributions
  CVM_Subsample.CVM_Algo
  "HOL-Decision_Procs.Approximation"
begin

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
  from assms step_2_preserves_finite_support[OF state_finite_support] state_finite_support have
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
  have \<open>finite (set_pmf (run_steps xs))\<close>
    using finite_run_state_pmf[where \<sigma>=\<open>FinalState xs\<close>] by simp
  thus ?case using 2 unfolding run_state_pmf.simps
    by (intro step_1_preserves_expectation_le[OF _ a]) auto
next
  case (3 xs x)
  let ?p = \<open>run_state_pmf (IntermState xs x)\<close>
  have c: \<open>AE state in ?p. card (state_chi state) \<le> threshold\<close>
    using card_run_state_pmf[where \<sigma>=\<open>IntermState xs x\<close>] by simp
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = ?p \<bind> step_2\<close>
    by (simp add:run_steps_snoc)
  have a: \<open>S \<subseteq> run_state_set (IntermState xs x)\<close> using 3(2) by auto
  have fin_S: \<open>finite S\<close> using a finite_run_state_set finite_subset by auto
  show ?case unfolding b
    using step_2_preserves_expectation_le[OF finite_run_state_pmf fin_S c] 3(1)[OF a] by simp
qed

end

definition \<open>state_p \<omega> = f^state_k \<omega>\<close>

context
  fixes q :: real and h :: \<open>real \<Rightarrow> real\<close>
  assumes
    \<open>0 < q\<close> \<open>q \<le> 1\<close> and
    \<open>concave_on {0 .. 1 / q} h\<close> and
    \<open>\<And> x. \<lbrakk>1 \<le> x; x * q \<le> 1\<rbrakk> \<Longrightarrow> h x \<ge> 0\<close>
begin

private abbreviation (input)
  \<open>aux' \<equiv> \<lambda> S x \<sigma>. (
    \<Prod> x \<in> S. of_bool (state_p \<sigma> \<ge> q) * h (of_bool (x \<in> state_chi \<sigma>) / state_p \<sigma>))\<close>

(* Lemma 3 *)
lemma run_steps_preserves_expectation_le' :
  assumes \<open>S \<subseteq> run_state_set \<sigma>\<close>
  shows
    \<open>measure_pmf.expectation (run_state_pmf \<sigma>) (aux' S x) \<le> (h 1) ^ card S\<close>
proof -
  show ?thesis sorry
qed

end

lemma of_bool_power:
  assumes \<open>y > 0\<close>
  shows \<open>((of_bool x)::real) ^ (y::nat) = of_bool x\<close>
  by (simp add: assms)

context
  fixes xs :: \<open>'a list\<close>
  assumes set_larger_than_threshold: \<open>card (set xs) \<ge> threshold\<close>
    (* If not the algorithm returns the correct result deterministically. *)
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

end


end (* end cvm_algo_proof *)

end (* end theory *)
