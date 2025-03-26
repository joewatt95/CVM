subsection \<open>Transforming eager to lazy sampling\<close>

theory Utils_PMF_Lazify

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Finite_Fields.Finite_Fields_More_PMF
  Utils_Reader_Monad

begin

locale lazify =
  fixes
    I :: \<open>'a set\<close> and
    d :: 'c and
    M :: \<open>'a \<Rightarrow> 'c pmf\<close>
  assumes fin_I: \<open>finite I\<close>
begin

definition space where \<open>space \<equiv> Pi_pmf I d M\<close>
definition sample where \<open>sample \<equiv> \<lambda> x. map_pmf (run_reader x) space\<close>

definition depends_on :: \<open>('a \<Rightarrow> 'c, 'b) reader_monad \<Rightarrow> 'a set \<Rightarrow> bool\<close> where
  \<open>depends_on \<equiv> \<lambda> m S. \<forall> f g.
    {f, g} \<subseteq> set_pmf space \<longrightarrow>
    (\<lambda> i \<in> S. f i) = (\<lambda> i \<in> S. g i) \<longrightarrow>
    run_reader m f = run_reader m g\<close>

lemma depends_onI:
  assumes "\<And> f g. \<lbrakk>f \<in> set_pmf space; g \<in> set_pmf space;
    restrict f S = restrict g S\<rbrakk> \<Longrightarrow> run_reader m f = run_reader m g"
  shows "depends_on m S"
  using assms unfolding depends_on_def by auto

lemma depends_onD:
  assumes
    "depends_on m S" and
    "f \<in> set_pmf space" "g \<in> set_pmf space" and
    "restrict f S = restrict g S"
  shows "run_reader m f = run_reader m g"
  using assms unfolding depends_on_def by blast

lemma depends_on_mono:
  assumes "depends_on m T" "T \<subseteq> S"
  shows "depends_on m S"
  using depends_onD[OF assms(1)] assms(2)
  by (intro depends_onI) (metis restrict_restrict inf.absorb_iff2)

lemma depends_on_restrict:
  "depends_on m S = depends_on m (S \<inter> I)"
proof -
  have a:"restrict f S = (\<lambda>i. if i \<in> (S \<inter> I) then f i else (if i \<in> S then d else undefined))"
    if "f \<in> set_pmf space" for f
    using that unfolding restrict_def space_def set_Pi_pmf[OF fin_I] PiE_dflt_def by auto

  have "depends_on m (S \<inter> I)" if "depends_on m S"
  proof (rule depends_onI)
    fix f g
    assume
      b:"f \<in> set_pmf space" "g \<in> set_pmf space" and
      c:"restrict f (S \<inter> I) = restrict g (S \<inter> I)"

    hence "restrict f S = restrict g S"
      unfolding a[OF b(1)] a[OF b(2)] by (intro ext if_cong refl) (metis restrict_apply')

    thus "run_reader m f = run_reader m g"
      using depends_onD[OF that] b by blast
  qed

  thus ?thesis using depends_on_mono by auto
qed

lemma depends_on_cong:
  assumes "S \<inter> I = T \<inter> I"
  assumes "\<And> x. x \<in> set_pmf space \<Longrightarrow> run_reader m x = run_reader n x"
  shows "depends_on m S \<longleftrightarrow> depends_on n T"
proof -
  have "depends_on m (S \<inter> I) = depends_on n (T \<inter> I)"
    using assms(1,2) unfolding depends_on_def by auto
  thus ?thesis using depends_on_restrict by auto
qed

lemma depends_on_univ: "depends_on f UNIV"
  unfolding depends_on_def by (simp add: restrict_UNIV)

lemma depends_on_return: "depends_on (return_rd c) S"
  unfolding depends_on_def return_rd_def by simp

lemma depends_on_bind:
  assumes "depends_on m S" "\<And>x. x \<in> set_pmf (sample m) \<Longrightarrow> depends_on (f x) S"
  shows "depends_on (bind_rd m f) S"
proof (rule depends_onI)
  fix x y :: "'a \<Rightarrow> 'c"
  assume a: "x \<in> set_pmf space" "y \<in> set_pmf space"  "restrict x S = restrict y S"
  have b: "run_reader m y \<in> set_pmf (sample m)" using a(2) unfolding sample_def by simp
  show "run_reader (m \<bind> f) x = run_reader (m \<bind> f) y"
    unfolding run_reader_simps depends_onD[OF assms(1) a] depends_onD[OF assms(2)[OF b] a] by simp
qed

lemma depends_on_bind_eq:
  assumes "\<And>w. w \<in> set_pmf (sample m) \<Longrightarrow> v \<in> set_pmf (sample (f w)) \<Longrightarrow>
    depends_on (map_rd ((=) w) m) S \<and> depends_on (map_rd ((=) v) (f w)) S"
  shows "depends_on (map_rd ((=) v) (bind_rd m f)) S"
proof (rule depends_onI)
  fix x y :: "'a \<Rightarrow> 'c"
  assume a: "x \<in> set_pmf space" "y \<in> set_pmf space" "restrict x S = restrict y S"

  let ?dep1 = "(\<lambda>w. depends_on (map_rd ((=) (run_reader m w)) m) S) "
  let ?dep2 = "(\<lambda>w. depends_on (map_rd ((=) v) (f (run_reader m w))) S)"

  have b:"?dep1 \<phi>" "?dep2 \<phi>" if "run_reader (f (run_reader m \<phi>)) \<phi> = v"
    "\<phi> \<in> set_pmf space" for \<phi>
  proof -
    let ?w = "run_reader m \<phi>"
    have "run_reader m \<phi> \<in> set_pmf (sample m) \<and> v \<in> set_pmf (sample (f ?w))"
      using that unfolding sample_def by auto
    thus "?dep1 \<phi>" "?dep2 \<phi>" using assms by auto
  qed

  have "run_reader (f (run_reader m x)) x = v \<longleftrightarrow> run_reader (f (run_reader m y)) y = v"
    using a depends_onD[OF b(1) a] depends_onD[OF b(2) a] unfolding run_reader_simps by metis
  thus "run_reader (map_rd ((=) v) (m \<bind> f)) x = run_reader (map_rd ((=) v) (m \<bind> f)) y"
    by auto 
qed

lemma depends_on_map :
  assumes "depends_on \<phi> S"
  shows "depends_on (map_rd f \<phi>) S"
  using assms
  unfolding map_rd_def by (intro depends_on_bind depends_on_return)

lemma depends_on_map_get :
  assumes "\<And> c1 c2.
    \<lbrakk>c1 \<in> set_pmf space; c2 \<in> set_pmf space; restrict c1 S = restrict c2 S\<rbrakk> \<Longrightarrow>
    f c1 = f c2"
  shows "depends_on (map_rd f get_rd) S"
  using assms
  apply (intro depends_onI)
  unfolding run_reader_simps by blast

definition independent_bind where
  "independent_bind m f \<equiv>
    \<forall> v. \<exists> I. depends_on (map_rd ((=) v) m) I \<and> depends_on (f v) (UNIV - I)"

lemma independent_bindI:
  assumes "\<And> v. depends_on (map_rd ((=) v) m) (F v) \<and> depends_on (f v) (UNIV - (F v))"
  shows "independent_bind m f"
  using assms unfolding independent_bind_def by auto

lemma lazify_bind:
  fixes m :: "('a \<Rightarrow> 'c, 'b) reader_monad"
  fixes f :: "'b \<Rightarrow> ('a \<Rightarrow> 'c, 'd) reader_monad"
  assumes "independent_bind m f"
  shows "sample (bind_rd m f) = sample m \<bind> (\<lambda>v. sample (f v))"
    (is "?L = ?R")
proof -
  let ?r = "\<lambda>x \<phi>. run_reader x \<phi>"

  define \<delta> where "\<delta> \<equiv> \<lambda> i. if i \<in> I then SOME x. x \<in> set_pmf (M i) else d"
  have \<delta>_ran_1: "\<delta> i \<in> set_pmf (M i)" if "i \<in> I" for i
    unfolding \<delta>_def using that set_pmf_not_empty by (auto simp:some_in_eq)
  have \<delta>_ran_2: "\<delta> i = d" if "i \<notin> I" for i using that unfolding \<delta>_def by simp

  have 0:"(\<lambda>i. if i \<in> J then f i else \<delta> i) \<in> set_pmf space"
    if "f \<in> Pi_pmf K d M" and "J \<subseteq> K" "K \<subseteq> I" for J K f
  proof -
    have fin_K: "finite K" using that fin_I finite_subset by metis
    show ?thesis using that \<delta>_ran_1 \<delta>_ran_2
      unfolding space_def set_Pi_pmf[OF fin_I] set_Pi_pmf[OF fin_K] PiE_dflt_def by auto
  qed

  have a:
    "map_pmf (\<lambda>\<phi>. let v = ?r m \<phi> in (v, ?r (f v) \<phi>)) space =
      sample m \<bind> (\<lambda>v. map_pmf (Pair v) (sample (f v)))"
    (is "?L1 = ?R1")
  proof (rule pmf_eqI)
    fix \<omega> :: "'b \<times> 'd"
    obtain J where J_dep:
      "depends_on (map_rd ((=) (fst \<omega>)) m) J" "depends_on (f (fst \<omega>)) (UNIV-J)"
      using assms(1) unfolding independent_bind_def by auto
    moreover have "I - J = (UNIV - J) \<inter> I" by blast
    ultimately have J_dep:"depends_on (map_rd ((=) (fst \<omega>)) m) (J\<inter>I)" "depends_on (f (fst \<omega>)) (I-J)"
      using depends_on_restrict by auto

    have fins: "finite (J \<inter> I)" "finite (I - J)" using fin_I by auto
    have b: "I = (J \<inter> I) \<union> (I - J)" by auto
    let ?q1 = "Pi_pmf (J \<inter> I) d M"
    let ?q2 = "Pi_pmf (I - J) d M"
    let ?c = "(\<lambda>(x,y) i. if i \<in> (J \<inter> I) then x i else y i)"
    let ?c1 = "(\<lambda>x i. if i \<in> (J \<inter> I) then x i else \<delta> i)"
    let ?c2 = "(\<lambda>x i. if i \<in> (I - J) then x i else \<delta> i)"
    let ?v = "fst \<omega>"
    let ?w = "snd \<omega>"

    have c_space: "?c (x, y) \<in> set_pmf space" if "x \<in> set_pmf ?q1" and "y \<in> set_pmf ?q2" for x y
      using that unfolding space_def set_Pi_pmf[OF fin_I] set_Pi_pmf[OF fins(1)]
        set_Pi_pmf[OF fins(2)] by (auto simp:PiE_dflt_def)

    have c:"?r m (?c (x,y)) = fst \<omega> \<longleftrightarrow> ?r m (?c1 x) = fst \<omega>"
      if "(x,y) \<in> set_pmf (pair_pmf ?q1 ?q2)" for x y
    proof -
      have "?r (map_rd ((=) (fst \<omega>)) m) (?c (x,y)) = ?r (map_rd ((=) (fst \<omega>)) m) (?c1 x)"
        using that
        apply (intro depends_onD[OF J_dep(1)] c_space 0) by auto
      hence "?r m (?c (x,y)) = fst \<omega> \<longleftrightarrow> ?r (map_rd ((=) (fst \<omega>)) m) (?c1 x) = True"
        by auto 
      also have "... \<longleftrightarrow>  ?r m (?c1 x) = fst \<omega>" by auto 
      finally show ?thesis by simp
    qed

    have d: "?r (f (fst \<omega>)) (?c (x,y)) = ?r (f (fst \<omega>)) (?c2 y)"
      if "(x,y) \<in> set_pmf (pair_pmf ?q1 ?q2)" for x y using that
      apply (intro depends_onD[OF J_dep(2)] 0 c_space)
      by auto

    have e:"?r m (?c1 x) = fst \<omega> \<longleftrightarrow> ?r m x = fst \<omega>"
      if "(x,y) \<in> set_pmf (pair_pmf space space)" for x y
    proof -
      have "?r (map_rd ((=) (fst \<omega>)) m) (?c1 x) = ?r (map_rd ((=) (fst \<omega>)) m) x" using that
        apply (intro depends_onD[OF J_dep(1)] 0)
        by (auto simp add: space_def)
      hence "?r m (?c1 x) = fst \<omega> \<longleftrightarrow> ?r (map_rd ((=) (fst \<omega>)) m) x = True" by auto
      also have "\<dots> \<longleftrightarrow> ?r m x = fst \<omega>" by auto 
      finally show ?thesis by simp
    qed

    have f: "?r (f (fst \<omega>)) (?c2 y) = ?r (f (fst \<omega>)) y" if "(x,y) \<in> set_pmf (pair_pmf space space)"
      for x y using that
      apply (intro depends_onD[OF J_dep(2)] 0)
      by (auto simp add: space_def)

    have "pmf ?L1 \<omega> = measure space {x. (run_reader m x, run_reader (f (run_reader m x)) x) = \<omega>}"
      unfolding pmf_map by (simp add:Let_def vimage_def)
    also have "\<dots> = measure (Pi_pmf ((J\<inter>I) \<union> (I-J)) d M) {x. ?r m x = ?v \<and> ?r (f (fst \<omega>)) x = ?w}"
      unfolding space_def
      by (intro arg_cong2[where f="measure_pmf.prob"] arg_cong[where f="\<lambda>I. Pi_pmf I d M"]) auto
    also have "\<dots> = measure (map_pmf ?c (pair_pmf ?q1 ?q2)) {x. ?r m x=?v \<and> ?r (f (fst \<omega>)) x=?w}"
      using fin_I by (intro arg_cong2[where f="measure_pmf.prob"] Pi_pmf_union) auto
    also have "\<dots> = measure (pair_pmf ?q1 ?q2) {(x,y). ?r m (?c (x,y))=?v\<and>?r (f ?v) (?c (x,y))=?w}"
      by (simp add:case_prod_beta' cong:if_cong)
    also have "\<dots> = measure (pair_pmf ?q1 ?q2) {(x,y). ?r m (?c1 x) = ?v \<and> ?r (f ?v) (?c2 y) = ?w}"
      using c d by (intro measure_pmf_cong) auto
    also have "\<dots> = measure (pair_pmf
      (map_pmf (\<lambda>f. restrict_dfl f (J \<inter> I) d) space) (map_pmf (\<lambda>f. restrict_dfl f (I-J) d) space))
      {(x,y). ?r m (?c1 x)=?v\<and>?r(f ?v) (?c2 y)=?w}"
      unfolding space_def restrict_dfl_def using fin_I by (intro arg_cong2[where f="pair_pmf"]
          arg_cong2[where f="measure_pmf.prob"] Pi_pmf_subset) auto
    also have "\<dots> = measure (pair_pmf space space) {(x,y). ?r m (?c1 x)=?v \<and> ?r (f ?v) (?c2 y)=?w}"
      by (simp flip: map_pair add: restrict_dfl_def case_prod_beta' cong: if_cong)
    also have "\<dots> = measure (pair_pmf space space) {(x,y). ?r m x = ?v \<and> ?r (f ?v) y = ?w}"
      using e f by (intro measure_pmf_cong) auto
    also have "\<dots> = (\<integral>x. measure (map_pmf (Pair x) space) {(x,y). ?r m x=?v\<and>?r(f ?v) y=?w} \<partial>space)"
      unfolding pair_pmf_def by (subst measure_bind_pmf) (simp add:map_pmf_def)
    also have "\<dots> = (\<integral>x. measure space {y. ?r m x = fst \<omega> \<and> ?r (f (fst \<omega>)) y = snd \<omega>} \<partial>space)"
      by (intro integral_cong_AE) simp_all
    also have "\<dots> = (\<integral>x. measure space {y. (?r m x, ?r (f (?r m x)) y) = \<omega>} \<partial>space)"
      by (intro integral_cong_AE AE_pmfI measure_pmf_cong) auto
    also have "\<dots> = pmf ?R1 \<omega>" unfolding pmf_bind pmf_map vimage_def sample_def by simp
    finally show "pmf ?L1 \<omega> = pmf ?R1 \<omega>" by simp
  qed

  have "?L = map_pmf snd (map_pmf (\<lambda>\<phi>. let v = run_reader m \<phi> in (v,run_reader (f v) \<phi>)) space)"
    unfolding map_pmf_comp sample_def
    by (intro map_pmf_cong refl) (simp add: Let_def)
  also have "\<dots> = map_pmf snd (bind_pmf (sample m) (\<lambda>v. map_pmf (Pair v) (sample (f v))))"
    unfolding a by simp
  also have "\<dots> = ?R" unfolding map_bind_pmf by (simp add:map_pmf_comp)
  finally show ?thesis .
qed

lemma lazify_return :
  "sample (return_rd x) = return_pmf x" (is "?L = ?R")
proof -
  have "?L = map_pmf (\<lambda> _. x) space" unfolding sample_def
    by (intro map_pmf_cong) simp_all 
  also have "\<dots> = ?R" by simp
  finally show ?thesis .
qed

lemma lazify_map :
  "sample (map_rd f m) = map_pmf f (sample m)" (is \<open>?L = ?R\<close>)
proof -
  have "?L = sample m \<bind> (\<lambda> v. sample (return_rd (f v)))"
    by (metis (no_types, lifting) bind_pmf_cong depends_on_return depends_on_univ independent_bind_def lazify_bind map_rd_def)
  also have "\<dots> = ?R" unfolding lazify_return map_pmf_def ..
  finally show ?thesis .
qed

end

end