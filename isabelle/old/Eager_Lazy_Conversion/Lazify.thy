theory Lazify
  imports
    Reader_Monad
    "Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF"
    "Finite_Fields.Finite_Fields_More_PMF"
begin

definition depends_on :: "('a \<Rightarrow> 'b, 'c) reader_monad \<Rightarrow> 'a set \<Rightarrow> bool"
  where
    "depends_on m S = (\<forall>f g. restrict f S = restrict g S \<longrightarrow> run_reader m f = run_reader m g)"

lemma depends_onI:
  assumes "\<And>f g. restrict f S = restrict g S \<Longrightarrow> run_reader m f = run_reader m g"
  shows "depends_on m S"
  using assms unfolding depends_on_def by metis

lemma depends_onD:
  assumes "depends_on m S" "restrict f S = restrict g S"
  shows "run_reader m f = run_reader m g"
  using depends_on_def assms by auto

lemma depends_on_cong:
  fixes m n :: "('a \<Rightarrow> 'b, 'c) reader_monad"
  assumes "S = T"
  assumes "\<And>x. run_reader m x = run_reader n x"
  shows "depends_on m S \<longleftrightarrow> depends_on n T"
  using assms unfolding depends_on_def by simp

lemma depends_on_univ: "depends_on f UNIV"
  unfolding depends_on_def by (simp add: restrict_UNIV)

lemma depends_on_return: "depends_on (return_rd c) S"
  unfolding depends_on_def return_rd_def by simp

lemma depends_on_mono:
  assumes "depends_on m T" "T \<subseteq> S"
  shows "depends_on m S"
  using depends_onD[OF assms(1)] assms(2)
  by (intro depends_onI) (metis restrict_restrict inf.absorb_iff2)

lemma depends_on_bind:
  fixes m :: "('i \<Rightarrow> 'c, 'a) reader_monad"
  fixes f :: "'a \<Rightarrow> ('i \<Rightarrow> 'c, 'b) reader_monad"
  assumes "depends_on m S" "\<And>x. depends_on (f (run_reader m x)) S"
  shows "depends_on (bind_rd m f) S"
proof (rule depends_onI)
  fix x y :: "'i \<Rightarrow> 'c"
  assume a:"restrict x S = restrict y S"
  show "run_reader (m \<bind> f) x = run_reader (m \<bind> f) y"
    unfolding run_reader_simps depends_onD[OF assms(1) a] depends_onD[OF assms(2) a] by simp
qed

lemma depends_on_bind_eq:
  fixes m :: "('i \<Rightarrow> 'c, 'a) reader_monad"
  fixes f :: "'a \<Rightarrow> ('i \<Rightarrow> 'c, 'b) reader_monad"
  assumes "\<And>w. w \<in> ran_rd m \<Longrightarrow> v \<in> ran_rd (f w) \<Longrightarrow>
    depends_on (map_rd ((=) w) m) S \<and> depends_on (map_rd ((=) v) (f w)) S"
  shows "depends_on (map_rd ((=) v) (bind_rd m f)) S"
proof (rule depends_onI)
  fix x y :: "'i \<Rightarrow> 'c"
  assume a:"restrict x S = restrict y S"

  let ?dep1 = "(\<lambda>w. depends_on (map_rd ((=) (run_reader m w)) m) S) "
  let ?dep2 = "(\<lambda>w. depends_on (map_rd ((=) v) (f (run_reader m w))) S)"

  have b:"?dep1 w" "?dep2 w" if "run_reader (f (run_reader m w)) w = v" for w
  proof -
    have "v \<in> ran_rd (f (run_reader m w)) \<and> run_reader m w \<in> ran_rd m"
      using that unfolding ran_rd_def by auto
    thus "?dep1 w" "?dep2 w" using assms by auto
  qed

  have "run_reader (f (run_reader m x)) x = v \<longleftrightarrow> run_reader (f (run_reader m y)) y = v"
    using depends_onD[OF b(1) a] depends_onD[OF b(2) a] unfolding run_reader_simps by metis
  thus "run_reader (map_rd ((=) v) (m \<bind> f)) x = run_reader (map_rd ((=) v) (m \<bind> f)) y"
    by (auto simp add:run_reader_simps)
qed

lemma depends_on_map:
  fixes f :: "('i \<Rightarrow> 'c) \<Rightarrow> 'a"
  assumes "\<And>c1 c2. restrict c1 S = restrict c2 S \<Longrightarrow> f c1 = f c2"
  shows "depends_on (map_rd f get_rd) S"
proof (rule depends_onI)
  fix c1 c2 :: "'i \<Rightarrow> 'c"
  assume "restrict c1 S = restrict c2 S"
  hence "f c1 = f c2" by (rule assms)
  thus "run_reader (map_rd f get_rd) c1 = run_reader (map_rd f get_rd) c2"
    by (simp add:run_reader_simps)
qed

definition independent_bind
  where "independent_bind m f = (\<forall>v. \<exists>I. depends_on (map_rd ((=) v) m) I \<and> depends_on (f v) (UNIV - I))"

lemma independent_bindI:
  assumes "\<And>v. depends_on (map_rd ((=) v) m) (F v) \<and> depends_on (f v) (UNIV - (F v))"
  shows "independent_bind m f"
  using assms unfolding independent_bind_def by auto

lemma lazify_bind:
  fixes I d p
  fixes m :: "('i \<Rightarrow> 'c, 'a) reader_monad"
  fixes f :: "'a \<Rightarrow> ('i \<Rightarrow> 'c, 'b) reader_monad"
  assumes "independent_bind m f" "finite I"
  defines "q \<equiv> Pi_pmf I d p"
  shows "map_pmf (run_reader (bind_rd m f)) q = bind_pmf (map_pmf (run_reader m) q) (\<lambda>x. map_pmf (run_reader (f x)) q)"
    (is "?L = ?R")
proof -
  let ?runr = "(\<lambda>x \<phi>. run_reader x \<phi>)"
  let ?run = "\<lambda>x. map_pmf (run_reader x) q"

  have a:"map_pmf (\<lambda>\<phi>. let v=?runr m \<phi> in (v,?runr (f v) \<phi>)) q = bind_pmf (?run m) (\<lambda>v. map_pmf (Pair v) (?run (f v)))"
    (is "?L1 = ?R1")
  proof (rule pmf_eqI)
    fix \<omega> :: "'a \<times> 'b"
    obtain J where J_dep: "depends_on (map_rd ((=) (fst \<omega>)) m) J" "depends_on (f (fst \<omega>)) (UNIV - J)"
      using assms(1) unfolding independent_bind_def by auto

    have fins: "finite (J \<inter> I)" "finite (I - J)" using assms(2) by auto
    have b: "I = (J \<inter> I) \<union> (I - J)" by auto
    let ?q1 = "Pi_pmf (J \<inter> I) d p"
    let ?q2 = "Pi_pmf (I - J) d p"
    let ?c = "(\<lambda>(x,y) i. if i \<in> (J \<inter> I) then x i else y i)"
    let ?c1 = "(\<lambda>x i. if i \<in> (J \<inter> I) then x i else d)"
    let ?c2 = "(\<lambda>x i. if i \<in> (I - J) then x i else d)"

    have c:"?runr m (?c (x,y)) = fst \<omega> \<longleftrightarrow> ?runr m x = fst \<omega>" if "(x,y) \<in> set_pmf (pair_pmf ?q1 ?q2)" for x y
    proof -
      have "\<And>i. i \<notin> J \<inter> I \<Longrightarrow> x i = d" "\<And>i. i \<notin> I - J \<Longrightarrow> y i = d"
        using that unfolding set_pair_pmf set_Pi_pmf[OF fins(1)]  set_Pi_pmf[OF fins(2)] PiE_dflt_def by force+
      hence cd:"?runr (map_rd ((=) (fst \<omega>)) m) (?c (x,y)) = ?runr (map_rd ((=) (fst \<omega>)) m) x"
        by (intro depends_onD[OF J_dep(1)]) auto
      hence "?runr m (?c (x,y)) = fst \<omega> \<longleftrightarrow> ?runr (map_rd ((=) (fst \<omega>)) m) x = True"
        by (auto simp: run_reader_simps)
      also have "... \<longleftrightarrow>  ?runr m x = fst \<omega>" by (auto simp: run_reader_simps)
      finally show ?thesis by simp
    qed

    have d: "?runr (f (fst \<omega>)) (?c (x,y)) = ?runr (f (fst \<omega>)) y"  for x y
      by (intro depends_onD[OF J_dep(2)]) auto

    have e:"?runr m (?c1 x) = fst \<omega> \<longleftrightarrow> ?runr m x = fst \<omega>" if "(x,y) \<in> set_pmf (pair_pmf q q)" for x y
    proof -
      have "\<And>i. i \<notin> I \<Longrightarrow> x i = d" "\<And>i. i \<notin> I \<Longrightarrow> y i = d"
        using that unfolding set_pair_pmf q_def set_Pi_pmf[OF assms(2)] PiE_dflt_def by force+
      hence cd:"?runr (map_rd ((=) (fst \<omega>)) m) (?c1 x) = ?runr (map_rd ((=) (fst \<omega>)) m) x"
        by (intro depends_onD[OF J_dep(1)]) auto
      hence "?runr m (?c1 x) = fst \<omega> \<longleftrightarrow> ?runr (map_rd ((=) (fst \<omega>)) m) x = True"
        by (auto simp: run_reader_simps)
      also have "... \<longleftrightarrow>  ?runr m x = fst \<omega>" by (auto simp: run_reader_simps)
      finally show ?thesis by simp
    qed

    have f: "?runr (f (fst \<omega>)) (?c2 y) = ?runr (f (fst \<omega>)) y" if "(x,y) \<in> set_pmf (pair_pmf q q)" for x y
    proof -
      have  "\<And>i. i \<notin> I \<Longrightarrow> y i = d"
        using that unfolding q_def set_Pi_pmf[OF assms(2)] set_pair_pmf PiE_dflt_def by simp
      thus ?thesis
        by (intro depends_onD[OF J_dep(2)]) auto
    qed

    have "pmf ?L1 \<omega> = measure_pmf.prob q {x. (run_reader m x, run_reader (f (run_reader m x)) x) = \<omega>}"
      unfolding pmf_map by (simp add:Let_def vimage_def)
    also have "... = measure (Pi_pmf ((J \<inter> I) \<union> (I-J)) d p) {x. ?runr m x = fst \<omega> \<and> ?runr (f (fst \<omega>)) x = snd \<omega>}"
      unfolding q_def by (intro arg_cong2[where f="measure_pmf.prob"] arg_cong[where f="\<lambda>I. Pi_pmf I d p"]) auto
    also have "... = measure (map_pmf ?c (pair_pmf ?q1 ?q2)) {x. ?runr m x = fst \<omega> \<and> ?runr (f (fst \<omega>)) x = snd \<omega>}"
      using assms(2) by (intro arg_cong2[where f="measure_pmf.prob"] Pi_pmf_union) auto
    also have "... = measure (pair_pmf ?q1 ?q2) {(x,y). ?runr m (?c (x,y))=fst \<omega> \<and> ?runr (f (fst \<omega>)) (?c (x,y))=snd \<omega>}"
      by (simp add:case_prod_beta' cong:if_cong)
    also have "... = measure (pair_pmf ?q1 ?q2) {(x,y). ?runr m x = fst \<omega> \<and> ?runr (f (fst \<omega>)) y = snd \<omega>}"
      using c d by (intro measure_pmf_cong) auto
    also have "... = measure(pair_pmf(map_pmf ?c1 q)(map_pmf ?c2 q)){(x,y). ?runr m x=fst \<omega>\<and>?runr(f(fst \<omega>))y=snd \<omega>}"
      unfolding q_def using assms(2)
      by (intro arg_cong2[where f="measure_pmf.prob"] arg_cong2[where f="pair_pmf"] Pi_pmf_subset) auto
    also have "... = measure (pair_pmf q q) {(x,y). ?runr m (?c1 x) = fst \<omega> \<and> ?runr (f (fst \<omega>)) (?c2 y) = snd \<omega>}"
      by (simp add:map_pair[symmetric] case_prod_beta' cong:if_cong)
    also have "... = measure (pair_pmf q q) {(x,y). ?runr m x = fst \<omega> \<and> ?runr (f (fst \<omega>)) y = snd \<omega>}"
      using e f by (intro measure_pmf_cong) auto
    also have "... = (\<integral>x. measure (map_pmf (Pair x) q) {(x,y). ?runr m x = fst \<omega> \<and> ?runr (f (fst \<omega>)) y = snd \<omega>} \<partial>q)"
      unfolding pair_pmf_def by (subst measure_bind_pmf) (simp add:map_pmf_def)
    also have "... = (\<integral>x. measure q {y. ?runr m x = fst \<omega> \<and> ?runr (f (fst \<omega>)) y = snd \<omega>} \<partial>q)"
      by (intro integral_cong_AE) simp_all
    also have "... = (\<integral>x. measure q {y. (run_reader m x, run_reader (f (run_reader m x)) y) = \<omega>} \<partial>q)"
      by (intro integral_cong_AE AE_pmfI measure_pmf_cong) auto
    also have "... = pmf ?R1 \<omega>" unfolding pmf_bind pmf_map vimage_def by simp
    finally show "pmf ?L1 \<omega> = pmf ?R1 \<omega>" by simp
  qed

  have "?L = map_pmf snd (map_pmf (\<lambda>\<phi>. let v = run_reader m \<phi> in (v,run_reader (f v) \<phi>)) q)"
    unfolding map_pmf_comp by (intro map_pmf_cong refl) (simp add:run_reader_simps Let_def)
  also have "... = map_pmf snd (bind_pmf (?run m) (\<lambda>v. map_pmf (Pair v) (?run (f v))))"
    unfolding a by simp
  also have "... = ?R"
    unfolding map_bind_pmf by (simp add:map_pmf_comp)
  finally show ?thesis
    by simp
qed

lemma lazify_return:
  "map_pmf (run_reader (return_rd x)) p = return_pmf x" (is "?L = ?R")
proof -
  have "?L = map_pmf (\<lambda>_. x) p" by (intro map_pmf_cong refl) (simp add:run_reader_simps)
  also have "... = ?R" by simp
  finally show ?thesis by simp
qed

lemma lazify_bind_return:
  assumes "finite I"
  shows
  "map_pmf (run_reader (bind_rd m (\<lambda>x. return_rd (f x)))) (Pi_pmf I d p) =
    map_pmf (run_reader m) (Pi_pmf I d p) \<bind> (\<lambda>x. return_pmf (f x))" (is "?L = ?R")
proof -
  have "?L = map_pmf (run_reader m) (Pi_pmf I d p) \<bind> (\<lambda>x. map_pmf (run_reader (return_rd (f x))) (Pi_pmf I d p))"
    by (intro assms lazify_bind independent_bindI[where F="(\<lambda>_. UNIV)"] depends_on_univ conjI depends_on_return)
  also have "... = ?R"
    unfolding lazify_return by simp
  finally show ?thesis by simp
qed

end