theory Utils_PMF_Basic

imports
  "Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF"
  "Finite_Fields.Finite_Fields_More_PMF"
  Utils_Basic

begin

lemma integrable_measure_pmf_pmf [simp] :
  \<open>integrable (measure_pmf p) <| \<lambda> x. pmf (f x) y\<close>
  apply (intro measure_pmf.integrable_const_bound[where B = 1])
  by (simp_all add: pmf_le_1)

lemma pmf_map_pred_true_eq_prob :
  \<open>pmf (map_pmf P p) True = \<P>(x in measure_pmf p. P x)\<close>
  by (simp add: measure_pmf_cong pmf_map)

(* abbreviation (input) kleisli_compose_left ::
  \<open>('a \<Rightarrow> 'b pmf) \<Rightarrow> ('b \<Rightarrow> 'c pmf) \<Rightarrow> 'a \<Rightarrow> 'c pmf\<close>
  (infixl \<open>>=>\<close> 50) where
  \<open>(f >=> g) \<equiv> \<lambda> x. bind_pmf (f x) g\<close>

abbreviation (input) kleisli_compose_right ::
  \<open>('b \<Rightarrow> 'c pmf) \<Rightarrow> ('a \<Rightarrow> 'b pmf) \<Rightarrow> 'a \<Rightarrow> 'c pmf\<close>
  (infixr \<open><=<\<close> 50) where
  \<open>(f <=< g) \<equiv> g >=> f\<close> *)

abbreviation \<open>foldM_pmf \<equiv> foldM bind_pmf return_pmf\<close>
abbreviation \<open>foldM_pmf_enumerate \<equiv> foldM_enumerate bind_pmf return_pmf\<close>

lemma map_pmf_times_one [simp] :
  fixes p :: \<open>nat pmf\<close>
  shows \<open>map_pmf ((*) <| Suc 0) p = p\<close>
  by (simp add: pmf.map_ident_strong)

lemma foldM_pmf_snoc :
  "foldM_pmf f (xs@[y]) val = bind_pmf (foldM_pmf f xs val) (f y)"
  by (induction xs arbitrary:val)
    (simp_all add: bind_return_pmf bind_return_pmf' bind_assoc_pmf cong:bind_pmf_cong)

lemma prod_pmf_reindex :
  assumes "finite T" "f ` S \<subseteq> T" "inj_on f S"
  shows "map_pmf (\<lambda> \<phi>. \<lambda> i \<in> S. \<phi> (f i)) (prod_pmf T F) = prod_pmf S (F \<circ> f)" (is "?L = ?R")
proof -
  have a:"finite S" using assms inj_on_finite by blast

  have "?L = map_pmf (\<lambda> \<phi>. \<lambda> i \<in> S. \<phi> (f i)) (map_pmf (\<lambda> \<omega>. \<lambda> x \<in> f ` S. \<omega> x) (prod_pmf T F))"
    unfolding map_pmf_comp restrict_def by (intro map_pmf_cong refl) (simp cong:if_cong)
  also have "... = map_pmf (\<lambda> \<phi>. \<lambda> i \<in> S. \<phi> (f i)) (prod_pmf (f ` S) F)"
    unfolding restrict_def by (intro map_pmf_cong refl Pi_pmf_subset[symmetric] assms(1,2))
  also have "... = prod_pmf S (F \<circ> f)" using a  assms(3)
  proof (induction S rule:finite_induct)
    case empty
    then show ?case by simp
  next
    case (insert x S)
    have "map_pmf (\<lambda> \<phi>. \<lambda> i \<in> insert x S. \<phi> (f i)) (prod_pmf (f ` (insert x S)) F) =
      map_pmf (\<lambda> \<phi>. \<lambda> i \<in> insert x S. \<phi> (f i)) (prod_pmf (insert (f x) (f ` S)) F)"
      using insert by simp
    also have "\<dots> = map_pmf (\<lambda>\<omega>. \<lambda>i\<in>insert x S. (\<lambda>(y, z). z(f x:=y)) \<omega> (f i)) (pair_pmf (F (f x)) (prod_pmf (f`S) F))"
      using insert(1,2,4) by (subst Pi_pmf_insert) (simp_all add:map_pmf_comp)
    also have "\<dots> = map_pmf (\<lambda>(\<omega>1,\<omega>2). \<lambda>i. if i=x then \<omega>1 else (if i \<in> S then \<omega>2 (f i) else undefined))
      (pair_pmf (F (f x)) (prod_pmf (f ` S) F))"
      using insert(1,2,4)
      by (intro map_pmf_cong refl ext) (auto simp add:case_prod_beta restrict_def rev_image_eqI cong:if_cong)
    also have "\<dots> =  map_pmf (\<lambda> (y, f). f(x := y))
      (map_pmf (\<lambda> (a, b). (id a, \<lambda> i \<in> S. b (f i))) (pair_pmf ((F \<circ> f) x) (prod_pmf (f ` S) F)))"
      unfolding map_pmf_comp comp_def by (intro map_pmf_cong refl) (simp add:restrict_def case_prod_beta' ext)
    also have "\<dots> = map_pmf (\<lambda> (y, f). f(x := y))
      (pair_pmf (map_pmf id ((F \<circ> f) x)) ((map_pmf (\<lambda> \<phi>. \<lambda> i \<in> S. \<phi> (f i)) (prod_pmf (f ` S) F))))"
      by (subst map_pair[symmetric]) auto
    also have "\<dots> = map_pmf (\<lambda> (y, f). f(x := y)) (pair_pmf ((F \<circ> f) x) (prod_pmf S (F \<circ> f)))"
      using insert(4) inj_on_subset by (subst insert(3)) auto
    also have "\<dots> = prod_pmf (insert x S) (F \<circ> f)"
      using insert by (intro Pi_pmf_insert[symmetric]) auto

    finally show ?case by blast
  qed
  finally show ?thesis by simp
qed

lemma bool_pmf_eqI :
  assumes "pmf p True = pmf q True"
  shows "p = q"
  using assms pmf_False_conv_True by (intro pmf_eqI) (metis (full_types))

text \<open>Better version of Pi_pmf_map.\<close>
lemma Pi_pmf_map' :
  assumes "finite I"
  shows
    "Pi_pmf I dflt (\<lambda> i. map_pmf (f i) (M i)) =
      map_pmf (\<lambda> x i. if i \<in> I then f i (x i) else dflt) (Pi_pmf I dflt' M)"
  unfolding map_pmf_def by (intro Pi_pmf_bind_return assms)

lemma prod_pmf_uncurry :
  fixes I :: "'a set" and J :: "'b set"
  assumes "finite I" "finite J"
  shows "prod_pmf (I \<times> J) M =
    map_pmf (\<lambda> \<omega>. \<lambda> (x, y) \<in> I \<times> J. \<omega> x y)
    (prod_pmf I (\<lambda> i. prod_pmf J (\<lambda> j. M (i,j))))" (is "?L = ?R")
proof -
  let ?map1 = "map_pmf (\<lambda> \<omega>. \<lambda> x \<in> I \<times> J. \<omega> (fst x) x)"
  let ?map2 = "map_pmf (\<lambda> \<omega>. \<lambda> x \<in> I \<times> J. \<omega> (fst x) (snd x))"

  have a: "inj_on snd ({i} \<times> J)" for i::'a
    by (intro inj_onI) auto

  have "?L =
    ?map1
      (Pi_pmf I \<lblot>undefined\<rblot>
        (\<lambda> i. prod_pmf ({x. fst x = i} \<inter> I \<times> J)
        (\<lambda> ij. M ij)))"
    using assms
    by (subst pi_pmf_decompose[where f="fst"])
      (simp_all add:restrict_dfl_def restrict_def vimage_def)

  also have "\<dots> = ?map1 (Pi_pmf I \<lblot>undefined\<rblot> (\<lambda> i. prod_pmf ({i} \<times> J) ((\<lambda> j. M (i, j)) \<circ> snd)))"
    by (intro map_pmf_cong Pi_pmf_cong refl) auto

  also have "\<dots> = ?map2 (prod_pmf I (\<lambda> i. prod_pmf J (\<lambda> j. M (i, j))))"
    apply (subst prod_pmf_reindex[OF assms(2) _ a, symmetric])
    by (simp_all
      add:
        Pi_pmf_map'[OF assms(1), where dflt' = undefined] map_pmf_comp
        case_prod_beta' restrict_def mem_Times_iff
      cong: if_cong)

  finally show ?thesis by (simp add: case_prod_beta')
qed

lemma prod_pmf_swap :
  fixes I :: "'a set" and J :: "'b set"
  assumes "finite I" "finite J"
  shows
    "prod_pmf (I\<times>J) M =
      map_pmf (\<lambda> \<omega>. \<omega> \<circ> prod.swap)
        (prod_pmf (J \<times> I) (M \<circ> prod.swap))" (is "?L = ?R")
proof -
  have f :"finite (I \<times> J)"
    using assms by auto
  have a: "inj_on prod.swap (J \<times> I)" for i :: 'a
    by (intro inj_onI) auto

  have "?R =
    map_pmf (\<lambda>\<omega>. \<omega> \<circ> prod.swap)
     (map_pmf (\<lambda> \<phi>. \<lambda> i \<in> J \<times> I. \<phi> (prod.swap i))
       (prod_pmf (I \<times> J) M))"
    by (simp add: f prod_pmf_reindex product_swap)

  also have "\<dots> = ?L"
    by (auto
      intro!: map_pmf_idI elim!: PiE_E
      simp add: map_pmf_comp comp_def set_prod_pmf[OF f] fun_eq_iff)

  finally show ?thesis by simp
qed

end