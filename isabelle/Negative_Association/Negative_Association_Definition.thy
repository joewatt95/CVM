section \<open>Definition\<close>

theory Negative_Association_Definition
  imports
    Concentration_Inequalities.Bienaymes_Identity
    CVM.Utils_Function (* for flip *)
    Negative_Association_Util
begin

context prob_space
begin

definition neg_assoc :: "('i \<Rightarrow> 'a \<Rightarrow> 'c :: {linorder_topology}) \<Rightarrow> 'i set \<Rightarrow> bool"
  where "neg_assoc X I = (
    (\<forall>i \<in> I. random_variable borel (X i)) \<and>
    (\<forall>f J. J \<subseteq> I \<and>
      (\<forall>\<iota><2. square_integrable M (f \<iota> \<circ> flip X) \<and> mono(f \<iota>) \<and> depends_on (f \<iota>) ([J,I-J]!\<iota>) \<and>
      f \<iota> \<in> PiM ([J,I-J]!\<iota>) (\<lambda>_. borel) \<rightarrow>\<^sub>M borel) \<longrightarrow>
      covariance (f 0 \<circ> flip X) (f 1 \<circ> flip X) \<le> 0))"

lemma neg_assocI:
  assumes "\<And>i. i \<in> I \<Longrightarrow> random_variable borel (X i)"
  assumes "\<And>f g J. J \<subseteq> I \<Longrightarrow>
    depends_on f J \<Longrightarrow> depends_on g (I-J) \<Longrightarrow>
    mono f \<Longrightarrow> mono g \<Longrightarrow>
    square_integrable M (f \<circ> flip X) \<Longrightarrow> square_integrable M (g \<circ> flip X) \<Longrightarrow>
    f \<in> PiM J (\<lambda>_. borel) \<rightarrow>\<^sub>M borel \<Longrightarrow> g \<in> PiM (I-J) (\<lambda>_. borel) \<rightarrow>\<^sub>M borel \<Longrightarrow>
    covariance (f \<circ> flip X) (g \<circ> flip X) \<le> 0"
  shows "neg_assoc X I"
  using assms unfolding neg_assoc_def by (auto simp:numeral_eq_Suc All_less_Suc)

lemma neg_assoc_empty:
  "neg_assoc X {}"
proof (intro neg_assocI, goal_cases)
  case (1 i)
  then show ?case by simp
next
  case (2 f g J)
  define fc gc where fc:"fc = f undefined" and gc:"gc = g undefined"

  have "depends_on f {}" "depends_on g {}" using 2 by auto
  hence fg_simps: "f = (\<lambda>x. fc)" "g = (\<lambda>x. gc)" unfolding fc gc using depends_on_empty by auto
  then show ?case unfolding fg_simps by (simp add:covariance_def prob_space)
qed

lemma neg_assoc_imp_measurable:
  assumes "neg_assoc X I"
  assumes "i \<in> I"
  shows "random_variable borel (X i)"
  using assms unfolding neg_assoc_def by auto

lemma neg_assoc_imp_mult_mono:
  fixes f g :: "('i \<Rightarrow> 'c::linorder_topology) \<Rightarrow> real"
  assumes "neg_assoc X I"
  assumes "J \<subseteq> I"
  assumes "square_integrable M (f \<circ> flip X)" "square_integrable M (g \<circ> flip X)"
  assumes "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) f" "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) g" (* e.g. if f,g are both mono inc. or both mono dec. *)
  assumes "depends_on f J" "depends_on g (I-J)"
  assumes "f \<in> borel_measurable (Pi\<^sub>M J (\<lambda>_. borel))" "g \<in> borel_measurable (Pi\<^sub>M (I-J) (\<lambda>_. borel))"
  shows
    "covariance (f \<circ> flip X) (g \<circ> flip X) \<le> 0"
    "(\<integral>\<omega>. f (\<lambda>i. X i \<omega>) * g (\<lambda>i. X i \<omega>) \<partial>M) \<le> expectation (f \<circ> flip X) * expectation (g \<circ> flip X)"
      (is "?L \<le> ?R")
proof -
  define q where "q \<iota> = (if \<iota> = 0 then f else g)" for \<iota> :: nat
  define h where "h \<iota> = ((*) (\<plusminus>\<^bsub>\<eta>\<^esub>)) \<circ> (q \<iota>)" for \<iota> :: nat
  let ?cov_alt = "(\<lambda>f g. (\<integral>\<omega>. (f \<omega> * g \<omega>) \<partial>M) - (\<integral>\<omega>. f \<omega> \<partial>M) * (\<integral>\<omega>. g \<omega> \<partial>M))"

  have 0: "square_integrable M ((*) (\<plusminus>\<^bsub>\<eta>\<^esub>)\<circ>\<phi>\<circ>flip X) = square_integrable M (\<phi>\<circ>flip X)" for \<phi>
    using assms(3) by (cases \<eta>) (simp_all add:comp_def)

  have 1:"square_integrable M (q \<iota> \<circ> flip X)" "depends_on (q \<iota>) ([J,I-J]!\<iota>)"
    "q \<iota> \<in> PiM ([J,I-J]!\<iota>) (\<lambda>_. borel) \<rightarrow>\<^sub>M borel"
    "mono ((*) (\<plusminus>\<^bsub>\<eta>\<^esub>) \<circ> q \<iota>)" if "\<iota> \<in> {0,1}" for \<iota>
    using that assms unfolding q_def conv_rel_to_sign by auto

  have 2: "((*) (\<plusminus>\<^bsub>\<eta>\<^esub>::real)) \<in> borel \<rightarrow>\<^sub>M borel" by simp

  have 3:"\<forall>\<iota><Suc (Suc 0). square_integrable M (h \<iota>\<circ>flip X)\<and>mono(h \<iota>) \<and> depends_on (h \<iota>) ([J,I-J]!\<iota>) \<and>
    h \<iota> \<in> PiM ([J,I-J]!\<iota>) (\<lambda>_. borel) \<rightarrow>\<^sub>M borel" unfolding All_less_Suc h_def
    by (intro conjI iffD2[OF 0] 1 depends_on_comp measurable_comp[OF _ 2]) simp_all

  have 4:"random_variable borel (q \<iota> \<circ> flip X)" if "\<iota> \<in> {0,1}"  for \<iota>
  proof -
    have "q \<iota> \<circ> flip X = q \<iota> \<circ> (\<lambda>\<omega>. \<lambda>i\<in>([J,I-J]!\<iota>). X i \<omega>)"
      using depends_onD[OF 1(2)[OF that]] unfolding comp_def by auto
    also have "... \<in> M \<rightarrow>\<^sub>M borel" using that assms(2) 1(3)[OF that]
      by (intro measurable_comp[OF measurable_restrict[OF neg_assoc_imp_measurable[OF assms(1)]]])
         auto
    finally show ?thesis by simp
  qed

  have 5:"random_variable borel (h \<iota> \<circ> flip X)" if "\<iota> \<in> {0,1}"  for \<iota>
    unfolding h_def comp_assoc by (intro that measurable_comp[OF 4 2])

  have "covariance (f \<circ> flip X) (g \<circ> flip X) = covariance (q 0 \<circ> flip X) (q 1 \<circ> flip X)"
    unfolding q_def by simp
  also have "... = ?cov_alt (q 0 \<circ> flip X) (q 1 \<circ> flip X)"
    using 1(1) by (intro covariance_eq 4) (simp_all add:comp_def)
  finally have 6: "covariance (f \<circ> flip X) (g \<circ> flip X) = ?cov_alt (q 0 \<circ> flip X) (q 1 \<circ> flip X)"
    by simp

  have "covariance (f \<circ> flip X) (g \<circ> flip X) = ?cov_alt (h 0 \<circ> flip X) (h 1 \<circ> flip X)"
    unfolding 6 using assms(3) unfolding h_def by (cases \<eta>, auto simp:comp_def)
  also have "... = covariance (h 0 \<circ> flip X) (h 1 \<circ> flip X)"
    using 3 by (intro covariance_eq[symmetric] 5) (auto simp:comp_def)
  also have "... \<le> 0" using 3 assms(1,2) numeral_2_eq_2 unfolding neg_assoc_def by metis
  finally show "covariance (f \<circ> flip X) (g \<circ> flip X) \<le> 0" by simp
  moreover have "covariance (f \<circ> flip X) (g \<circ> flip X) = ?L - ?R" unfolding 6 q_def by simp
  ultimately show "?L \<le> ?R" by simp
qed

(* Property P4 \cite[Property P2]{joagdev1982} *)
lemma neg_assoc_subset:
  assumes "J \<subseteq> I"
  assumes "neg_assoc X I"
  shows "neg_assoc X J"
proof (rule neg_assocI,goal_cases)
  case (1 i)
  then show ?case using neg_assoc_imp_measurable[OF assms(2)] assms(1) by auto
next
  case (2 f g K)
  have a:"K \<subseteq> I" using 2 assms(1) by auto
  have b:"1 \<in> {-1,1::real}" by simp

  have "g = g \<circ> (\<lambda>m. restrict m (J-K))"
    using 2 depends_onD unfolding comp_def by (intro ext) auto
  also have "... \<in> borel_measurable (Pi\<^sub>M (I - K) (\<lambda>_. borel))"
    using 2 assms(1) by (intro measurable_comp[OF measurable_restrict_subset]) auto
  finally have "g \<in> borel_measurable (Pi\<^sub>M (I - K) (\<lambda>_. borel))" by simp
  moreover have "depends_on g (I-K)" using depends_on_mono assms(1) 2
    by (metis Diff_mono dual_order.eq_iff)
  ultimately show "covariance (f \<circ> flip X) (g \<circ> flip X) \<le> 0"
    using 2 by (intro neg_assoc_imp_mult_mono[OF assms(2) a, where \<eta>="Fwd"]) (simp_all add:comp_def)
qed

lemma lim_min_n: "(\<lambda>n. min (real n) x) \<longlonglongrightarrow> x"
proof -
  define m where "m = nat \<lceil>x\<rceil>"
  have "min (real (n+m)) x = x" for n unfolding m_def by (intro min_absorb2) linarith
  hence "(\<lambda>n. min (real (n+m)) x) \<longlonglongrightarrow> x" by simp
  thus ?thesis using LIMSEQ_offset[where k="m"] by fast
qed

lemma neg_assoc_imp_mult_mono_nonneg:
  fixes f g :: "('i \<Rightarrow> 'c::linorder_topology) \<Rightarrow> real"
  assumes "neg_assoc X I" "J \<subseteq> I"
  assumes "range f \<subseteq> {0..}" "range g \<subseteq> {0..}"
  assumes "integrable M (f \<circ> flip X)" "integrable M (g \<circ> flip X)"
  assumes "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) f" "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) g"
  assumes "depends_on f J" "depends_on g (I-J)"
  assumes "f \<in> borel_measurable (Pi\<^sub>M J (\<lambda>_. borel))" "g \<in> borel_measurable (Pi\<^sub>M (I-J) (\<lambda>_. borel))"
  shows "has_int_that M (\<lambda>\<omega>. f (flip X \<omega>) * g (flip X \<omega>))
    (\<lambda>r. r \<le> expectation (f\<circ>flip X) * expectation (g\<circ>flip X))"
proof -
  let ?cf = "(\<lambda>n x. min (real n) (f x))"
  let ?cg = "(\<lambda>n x. min (real n) (g x))"

  define u where "u = (\<lambda>\<omega>. f (\<lambda>i. X i \<omega>) * g (\<lambda>i. X i \<omega>))"
  define h where "h n \<omega> = ?cf n  (\<lambda>i. X i \<omega>) * ?cg n (\<lambda>i. X i \<omega>)" for n \<omega>
  define x where "x = (SUP n. expectation (h n))"

  note borel_intros = borel_measurable_times borel_measurable_const borel_measurable_min
    borel_measurable_power
  note bounded_intros' = integrable_bounded bounded_intros bounded_const_min

  have f_meas: "random_variable borel (\<lambda>x. f (\<lambda>i. X i x))"
    using borel_measurable_integrable[OF assms(5)] by (simp add:comp_def)
  have g_meas: "random_variable borel (\<lambda>x. g (\<lambda>i. X i x))"
    using borel_measurable_integrable[OF assms(6)] by (simp add:comp_def)

  have h_int: "integrable M (h n)" for n
    unfolding h_def using assms(3,4) by (intro bounded_intros' borel_intros f_meas g_meas) fast+

  have exp_h_le_R: "expectation (h n) \<le> expectation (f\<circ>flip X) * expectation (g\<circ>flip X)" for n
  proof -
    have "square_integrable M ((\<lambda>a. min (real n) (f a)) \<circ> (\<lambda>x y. X y x))"
      using assms(3) unfolding comp_def
      by (intro bounded_intros' bdd_belowI[where m="0"] borel_intros f_meas) auto
    moreover have "square_integrable M ((\<lambda>a. min (real n) (g a)) \<circ> (\<lambda>x y. X y x))"
      using assms(4) unfolding comp_def
      by (intro bounded_intros' bdd_belowI[where m="0"] borel_intros g_meas) auto
    moreover have "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) ((\<lambda>a. min (real n) (f a)))"
      using monotoneD[OF assms(7)] unfolding comp_def min_mult_distrib_left
      by (intro monotoneI) (cases "\<eta>", fastforce+)
    moreover have "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) ((\<lambda>a. min (real n) (g a)))"
      using monotoneD[OF assms(8)] unfolding comp_def min_mult_distrib_left
      by (intro monotoneI) (cases \<eta>, fastforce+)
    ultimately have "expectation (h n) \<le> expectation (?cf n\<circ>flip X) * expectation (?cg n\<circ>flip X)"
      unfolding h_def by (intro neg_assoc_imp_mult_mono[OF assms(1-2)] borel_intros assms(11,12)
          depends_on_comp_2[OF assms(10)] depends_on_comp_2[OF assms(9)]) auto
    also have "... \<le> expectation (f\<circ>flip X) * expectation (g\<circ>flip X)"
      using assms(3,4) by (intro mult_mono integral_nonneg_AE AE_I2 integral_mono' assms(5,6)) auto
    finally show ?thesis by simp
  qed

  have h_mono_ptw: "AE \<omega> in M. mono (\<lambda>n. h n \<omega>)"
    using assms(3,4) unfolding h_def by (intro AE_I2 monoI mult_mono) auto
  have h_mono: "mono (\<lambda>n. expectation (h n))"
    by (intro monoI integral_mono_AE AE_mp[OF h_mono_ptw AE_I2] h_int) (simp add:mono_def)

  have "random_variable borel u" using f_meas g_meas unfolding u_def by (intro borel_intros)
  moreover have "AE \<omega> in M. (\<lambda>n. h n \<omega>) \<longlonglongrightarrow> u \<omega>"
    unfolding h_def u_def by (intro tendsto_mult lim_min_n AE_I2)
  moreover have "bdd_above (range (\<lambda>n. expectation (h n)))"
    using exp_h_le_R by (intro bdd_aboveI) auto
  hence "(\<lambda>n. expectation (h n)) \<longlonglongrightarrow> x"
    using LIMSEQ_incseq_SUP[OF _ h_mono] unfolding x_def by simp
  ultimately have "has_bochner_integral M u x" using h_int h_mono_ptw
    by (intro has_bochner_integral_monotone_convergence[where f="h"])
  moreover have "x \<le> expectation (f\<circ>flip X) * expectation (g\<circ>flip X)"
    unfolding x_def by (intro cSUP_least exp_h_le_R) simp
  ultimately show ?thesis unfolding has_bochner_integral_iff u_def has_int_that_def by auto
qed

(* Property P2 \cite[Property P2]{joagdev1982} *)
lemma neg_assoc_imp_prod_mono:
  fixes f :: "'i \<Rightarrow> ('c::linorder_topology) \<Rightarrow> real"
  assumes "finite I"
  assumes "neg_assoc X I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> integrable M (f i \<circ> X i) \<and> monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (f i) \<and> range (f i)\<subseteq>{0..}"
  assumes "\<And>i. i \<in> I \<Longrightarrow> f i \<in> borel_measurable borel"
  shows "has_int_that M (\<lambda>\<omega>. (\<Prod>i\<in>I. (f i \<circ> X i) \<omega>)) (\<lambda>r. r \<le> (\<Prod>i\<in> I. expectation (f i \<circ> X i)))"
  using assms
proof (induction I rule:finite_induct)
  case empty then show ?case by (simp add:has_int_that_def)
next
  case (insert x F)

  define g where "g v = f x (v x)" for v
  define h where "h v = (\<Prod>i\<in>F. f i (v i))" for v

  have 0: "{x} \<subseteq> insert x F" by auto

  have ran_g: "range g \<subseteq> {0..}" using insert(5) unfolding g_def by auto

  have "True = has_int_that M (\<lambda>\<omega>. \<Prod>i\<in>F. (f i \<circ> X i) \<omega>) (\<lambda>r. r \<le> (\<Prod>i\<in>F. expectation (f i \<circ> X i)))"
    by (intro true_eq_iff insert neg_assoc_subset[OF _ insert(4)]) auto
  also have "... = has_int_that M (h \<circ> flip X) (\<lambda>r. r \<le> (\<Prod>i\<in>F. expectation (f i \<circ> X i)))"
    unfolding h_def by (intro arg_cong2[where f="has_int_that M"] refl)(simp add:comp_def)
  finally have 2: "has_int_that M (h \<circ> flip X) (\<lambda>r. r \<le> (\<Prod>i\<in>F. expectation (f i \<circ> X i)))" by simp

  have "(\<Prod>i\<in>F. f i (v i)) \<ge> 0" for v using insert(5) by (intro prod_nonneg) auto
  hence "range h \<subseteq> {0..}" unfolding h_def by auto
  moreover have "integrable M (g \<circ> flip X)" unfolding g_def using insert(5) by (auto simp:comp_def)
  moreover have 3:"monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (f x)" using insert(5) by simp
  have "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) g" using monotoneD[OF 3]
    unfolding g_def by (intro monotoneI) (auto simp:comp_def le_fun_def)
  moreover have 4:"monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (f i)" "\<And>x. f i x \<ge> 0" if "i \<in> F" for i using that insert(5) by auto
  hence "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) h" using monotoneD[OF 4(1)] unfolding h_def
    by (intro monotoneI) (cases \<eta>, auto intro:prod_mono simp:comp_def le_fun_def)
  moreover have "depends_on g {x}" unfolding g_def by (intro depends_onI) force
  moreover have "depends_on h F"
    unfolding h_def by (intro depends_onI prod.cong refl) force
  hence "depends_on h (F - {x})" using insert(2) by simp
  moreover have "g \<in> borel_measurable (Pi\<^sub>M {x} (\<lambda>_. borel))" unfolding g_def
    by (intro measurable_compose[OF _ insert(6)] measurable_component_singleton) auto
  moreover have "h \<in> borel_measurable (Pi\<^sub>M F (\<lambda>_. borel))"
    unfolding h_def by (intro borel_measurable_prod measurable_compose[OF _ insert(6)]
        measurable_component_singleton) auto
  hence "h \<in> borel_measurable (Pi\<^sub>M (F - {x}) (\<lambda>_. borel))" using insert(2) by simp
  ultimately have "True = has_int_that M (\<lambda>\<omega>. g (flip X \<omega>) * h (flip X \<omega>))
    (\<lambda>r. r \<le> expectation (g \<circ> flip X) * expectation (h \<circ> flip X))"
    by (intro true_eq_iff neg_assoc_imp_mult_mono_nonneg[OF insert(4) 0, where \<eta>="\<eta>"]
        ran_g has_int_thatD[OF 2]) simp_all
  also have "\<dots> = has_int_that M (\<lambda>\<omega>. (\<Prod>i\<in>insert x F. (f i \<circ> X i) \<omega>))
    (\<lambda>r. r \<le> expectation (g \<circ> flip X) * expectation (h \<circ> flip X))"
    unfolding g_def h_def using insert(1,2) by (intro arg_cong2[where f="has_int_that M"] refl) simp
  also have "\<dots> \<le> has_int_that M (\<lambda>\<omega>. (\<Prod>i\<in>insert x F. (f i \<circ> X i) \<omega>))
    (\<lambda>r. r \<le> expectation (g \<circ> flip X) * (\<Prod>i \<in> F. expectation (f i \<circ> X i)))"
    using ran_g has_int_thatD[OF 2] by (intro has_int_that_mono le_trans mult_left_mono
        integral_nonneg_AE AE_I2) (auto simp: comp_def)
  also have "\<dots> = has_int_that M
    (\<lambda>\<omega>. \<Prod>i\<in>insert x F. (f i \<circ> X i) \<omega>) (\<lambda>r. r \<le> (\<Prod>i\<in>insert x F. expectation (f i \<circ> X i)))"
    using insert(1,2) by (intro arg_cong2[where f="has_int_that M"] refl) (simp add:g_def comp_def)
  finally show ?case using le_boolE by blast
qed

(* Property P5 *)

lemma neg_assoc_compose:
  fixes f :: "'j \<Rightarrow> ('i \<Rightarrow> ('c::linorder_topology)) \<Rightarrow> ('d ::linorder_topology)"
  assumes "finite I"
  assumes "\<And>j. j \<in> J \<Longrightarrow> deps j \<subseteq> I"
  assumes "\<And>j1 j2. j1 \<in> J \<Longrightarrow> j2 \<in> J \<Longrightarrow> j1 \<noteq> j2 \<Longrightarrow> deps j1 \<inter> deps j2 = {}"
  assumes "\<And>j. j \<in> J \<Longrightarrow> depends_on (f j) (deps j) \<and> monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (f j)"
  assumes "neg_assoc X I"
  assumes "\<And>j. j \<in> J \<Longrightarrow> f j \<in> borel_measurable (PiM (deps j) (\<lambda>_. borel))"
  shows "neg_assoc (\<lambda>j \<omega>. f j (\<lambda>i\<in>I. X i \<omega>)) J"
proof (rule neg_assocI, goal_cases)
  case (1 i)
  then show ?case sorry
next
  case (2 g h K)


  show "covariance (g \<circ> (\<lambda>x y. f y (\<lambda>i\<in>I. X i x))) (h \<circ> (\<lambda>x y. f y (\<lambda>i\<in>I. X i x))) \<le> 0"
    sorry
qed

end


end