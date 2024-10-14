theory Utils_PMF

imports
  "Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF"
  "Finite_Fields.Finite_Fields_More_PMF"
  CVM.Utils_Function

begin

abbreviation foldM_pmf ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b pmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b pmf\<close> where
  \<open>foldM_pmf \<equiv> foldM bind_pmf return_pmf\<close>

lemma bernoulli_pmf_one [simp] :
  \<open>bernoulli_pmf 1 = return_pmf True\<close>

  by (simp add: bernoulli_pmf.rep_eq pmf_eqI)

lemma binomial_pmf_one [simp] :
  \<open>binomial_pmf n 1 = return_pmf n\<close>

  by (metis set_pmf_binomial_1 set_pmf_subset_singleton subset_iff_psubset_eq)

lemma map_pmf_times_one [simp] :
  fixes p :: \<open>nat pmf\<close>
  shows \<open>map_pmf ((*) <| Suc 0) p = p\<close>

  by (simp add: pmf.map_ident_strong)

(* definition p::"bool pmf"
  where "p = bernoulli_pmf (1/2)"

definition q::"bool pmf"
  where "q = do {
    c1 \<leftarrow> bernoulli_pmf (1/2);
    c2 \<leftarrow> bernoulli_pmf (1/2);
    return_pmf (c1 = c2)
  }"

lemma rel_pmf_p_q:
  shows "rel_pmf (=) p q"
proof -
  let ?p = "p \<bind> (\<lambda> x. return_pmf x \<bind> return_pmf)"

  have "rel_pmf (=) ?p q"
    unfolding p_def q_def

    apply (rule rel_pmf_bindI[
      where ?R = "\<lambda> x y. x \<in> bernoulli_pmf (1/2) \<and> x = y"])

    apply (blast intro: rel_pmf_reflI)

    apply (rule rel_pmf_bindI[
      where ?R = "\<lambda> x y. x \<in> bernoulli_pmf (1/2) \<and> y \<in> bernoulli_pmf (1/2)"])

    apply (simp add: rel_pmf_return_pmf1)

    apply (subst rel_return_pmf)

    sorry

  then show ?thesis by (simp add: bind_return_pmf')
qed *)

lemma foldM_pmf_snoc: "foldM_pmf f (xs@[y]) val = bind_pmf (foldM_pmf f xs val) (f y)"
  by (induction xs arbitrary:val)
    (simp_all add: bind_return_pmf bind_return_pmf' bind_assoc_pmf cong:bind_pmf_cong)


lemma prod_pmf_reindex:
  assumes "finite T" "f ` S \<subseteq> T" "inj_on f S"
  shows "map_pmf (\<lambda>\<phi>. \<lambda>i \<in> S. \<phi> (f i)) (prod_pmf T F) = prod_pmf S (F \<circ> f)" (is "?L = ?R")
proof -
  have a:"finite S" using assms inj_on_finite by blast

  have "?L = map_pmf (\<lambda>\<phi>. \<lambda>i \<in> S. \<phi> (f i)) (map_pmf (\<lambda>\<omega>. \<lambda>x\<in>f ` S. \<omega> x) (prod_pmf T F))"
    unfolding map_pmf_comp restrict_def by (intro map_pmf_cong refl) (simp cong:if_cong)
  also have "... = map_pmf (\<lambda>\<phi>. \<lambda>i \<in> S. \<phi> (f i)) (prod_pmf (f ` S) F)"
    unfolding restrict_def by (intro map_pmf_cong refl Pi_pmf_subset[symmetric] assms(1,2))
  also have "... = prod_pmf S (F \<circ> f)" using a  assms(3)
  proof (induction S rule:finite_induct)
    case empty
    then show ?case by simp
  next
    case (insert x S)
    have "map_pmf (\<lambda>\<phi>. \<lambda>i\<in>insert x S. \<phi> (f i)) (prod_pmf (f`(insert x S)) F) =
      map_pmf (\<lambda>\<phi>. \<lambda>i\<in>insert x S. \<phi> (f i)) (prod_pmf (insert (f x) (f`S)) F)"
      using insert by simp
    also have "... = map_pmf (\<lambda>\<omega>. \<lambda>i\<in>insert x S. (\<lambda>(y, z). z(f x:=y)) \<omega> (f i)) (pair_pmf (F (f x)) (prod_pmf (f`S) F))"
      using insert(1,2,4) by (subst Pi_pmf_insert) (simp_all add:map_pmf_comp)
    also have "... = map_pmf (\<lambda>(\<omega>1,\<omega>2). \<lambda>i. if i=x then \<omega>1 else (if i \<in> S then \<omega>2 (f i) else undefined))
      (pair_pmf (F (f x)) (prod_pmf (f ` S) F))"
      using insert(1,2,4)
      by (intro map_pmf_cong refl ext) (auto simp add:case_prod_beta restrict_def rev_image_eqI cong:if_cong)
    also have "... =  map_pmf (\<lambda>(y, f). f(x := y))
      (map_pmf (\<lambda>(a, b). (id a, \<lambda>i\<in>S. b (f i))) (pair_pmf ((F \<circ> f) x) (prod_pmf (f ` S) F)))"
      unfolding map_pmf_comp comp_def by (intro map_pmf_cong refl) (simp add:restrict_def case_prod_beta' ext)
    also have "... = map_pmf (\<lambda>(y, f). f(x := y))
      (pair_pmf (map_pmf id ((F \<circ> f) x)) ((map_pmf (\<lambda>\<phi>. \<lambda>i\<in>S. \<phi> (f i)) (prod_pmf (f ` S) F))))"
      by (subst map_pair[symmetric]) auto
    also have "... = map_pmf (\<lambda>(y, f). f(x := y)) (pair_pmf ((F \<circ> f) x) (prod_pmf S (F \<circ> f)))"
      using insert(4) inj_on_subset by (subst insert(3)) auto
    also have "... = prod_pmf (insert x S) (F \<circ> f)"
      using insert by (intro Pi_pmf_insert[symmetric]) auto

    finally show ?case by blast
  qed
  finally show ?thesis by simp
qed

lemma bool_pmf_eqI:
  assumes "pmf p True = pmf q True"
  shows "p = q"
  using assms pmf_False_conv_True by (intro pmf_eqI) (metis (full_types))

end