section \<open>PMF utilities\<close>

text \<open>This section provides various PMF related utilities.\<close>

theory Utils_PMF_Basic

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Finite_Fields.Finite_Fields_More_PMF
  Utils_Basic

begin

subsection \<open>Basic PMF utilities\<close>

lemma integrable_measure_pmf_pmf [simp] :
  \<open>integrable (measure_pmf p) <| \<lambda> x. pmf (f x) y\<close>
  apply (intro measure_pmf.integrable_const_bound[where B = 1])
    by (simp_all add: pmf_le_1)

lemma pmf_map_pred_true_eq_prob :
  \<open>pmf (map_pmf P p) True = \<P>(x in measure_pmf p. P x)\<close>
  by (simp add: measure_pmf_cong pmf_map)

lemma map_pmf_times_one [simp] :
  \<open>map_pmf ((*) <| Suc 0) p = p\<close>
  by (simp add: pmf.map_ident_strong)

lemma prod_pmf_reindex :
  assumes "finite T" "f ` S \<subseteq> T" "inj_on f S"
  shows
    "map_pmf (\<lambda> \<phi>. \<lambda> i \<in> S. \<phi> (f i)) (prod_pmf T F) = prod_pmf S (F <<< f)"
    (is "?L = ?R")
proof -
  have a:"finite S" using assms inj_on_finite by blast

  have "?L = map_pmf (\<lambda> \<phi>. \<lambda> i \<in> S. \<phi> (f i)) (map_pmf (\<lambda> \<omega>. \<lambda> x \<in> f ` S. \<omega> x) (prod_pmf T F))"
    unfolding map_pmf_comp restrict_def by (intro map_pmf_cong refl) (simp cong:if_cong)
  also have "\<dots> = map_pmf (\<lambda> \<phi>. \<lambda> i \<in> S. \<phi> (f i)) (prod_pmf (f ` S) F)"
    unfolding restrict_def by (intro map_pmf_cong refl Pi_pmf_subset[symmetric] assms(1,2))
  also have "\<dots> = prod_pmf S (F <<< f)" using a assms(3)
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
      (map_pmf (\<lambda> (a, b). (id a, \<lambda> i \<in> S. b (f i))) (pair_pmf ((F <<< f) x) (prod_pmf (f ` S) F)))"
      unfolding map_pmf_comp comp_def by (intro map_pmf_cong refl) (simp add:restrict_def case_prod_beta' ext)
    also have "\<dots> = map_pmf (\<lambda> (y, f). f(x := y))
      (pair_pmf (map_pmf id (F <| f x)) ((map_pmf (\<lambda> \<phi>. \<lambda> i \<in> S. \<phi> (f i)) (prod_pmf (f ` S) F))))"
      by (subst map_pair[symmetric]) auto
    also have "\<dots> = map_pmf (\<lambda> (y, f). f(x := y)) (pair_pmf (F <| f x) (prod_pmf S (F <<< f)))"
      using insert(4) inj_on_subset by (subst insert(3)) (auto simp add: comp_def)
    also have "\<dots> = prod_pmf (insert x S) (F <<< f)"
      using insert by (intro Pi_pmf_insert[symmetric]) auto

    finally show ?case by blast
  qed
  finally show ?thesis by simp
qed

lemma bool_pmf_eq_iff_pmf_True_eq :
  \<open>p = q \<longleftrightarrow> pmf p True = pmf q True\<close>
  by (smt (verit, best) pmf_neq_exists_less)

subsubsection \<open>Properties about Pi\_pmf and prod\_pmf\<close>

text \<open>Better version of Pi\_pmf\_map.\<close>
lemma Pi_pmf_map' :
  assumes "finite I"
  shows
    "Pi_pmf I dflt (\<lambda> i. map_pmf (f i) (M i)) =
      map_pmf (\<lambda> x i. if i \<in> I then f i (x i) else dflt) (Pi_pmf I dflt' M)"
  unfolding map_pmf_def by (intro Pi_pmf_bind_return assms)

context
  fixes I :: \<open>'a set\<close> and J :: \<open>'b set\<close>
  assumes finsets [simp] : \<open>finite I\<close> \<open>finite J\<close>
begin

lemma prod_pmf_uncurry :
  "prod_pmf (I \<times> J) M =
    map_pmf (\<lambda> \<omega>. \<lambda> (i, j) \<in> I \<times> J. \<omega> i j)
    (prod_pmf I (\<lambda> i. prod_pmf J (\<lambda> j. M (i, j))))"
  (is "?L = ?R")
proof -
  let ?map =
    \<open>map_pmf (\<lambda> \<omega>. \<lambda> ij \<in> I \<times> J. \<omega> (fst ij) ij)
      <<< Pi_pmf I \<lblot>undefined\<rblot>\<close>

  have \<open>?L = ?map (\<lambda> i. prod_pmf ({ij. fst ij = i} \<inter> I \<times> J) M)\<close>
    by (subst pi_pmf_decompose[where f = fst])
      (simp_all add: restrict_dfl_def restrict_def vimage_def)

  also have \<open>\<dots> = ?map (\<lambda> i. prod_pmf ({i} \<times> J) M)\<close>
    by (fastforce intro: map_pmf_cong Pi_pmf_cong)

  also have \<open>\<dots> =
    ?map (\<lambda> i. map_pmf
      (\<lambda> \<phi>. \<lambda> i \<in> {i} \<times> J. \<phi> (snd i))
      (prod_pmf J <| \<lambda> j. M (i, j)))\<close>
    apply (subst prod_pmf_reindex)
      by (fastforce intro: inj_onI map_pmf_cong Pi_pmf_cong)+

  also have \<open>\<dots> = ?R\<close>
    unfolding
      Pi_pmf_map'[OF finsets(1), where dflt' = undefined]
      map_pmf_comp case_prod_beta
    by (fastforce intro: map_pmf_cong)

  finally show ?thesis .
qed

lemma prod_pmf_swap :
  "prod_pmf (I \<times> J) M =
    map_pmf (\<lambda> \<omega> (i, j). \<omega> (j, i))
      (prod_pmf (J \<times> I) (\<lambda> (i, j). M (j, i)))"
  (is "?L = ?R")
proof -
  have "?R =
    map_pmf (\<lambda> \<omega> (i, j). \<omega> (j, i))
      (map_pmf (\<lambda> \<phi>. \<lambda> (j, i) \<in> J \<times> I. \<phi> (i, j))
      (prod_pmf (I \<times> J) M))"
    unfolding case_prod_beta
    apply (subst prod_pmf_reindex)
    by (auto intro: inj_onI simp add: comp_def)

  also have "\<dots> = ?L"
    unfolding map_pmf_comp case_prod_beta
    by (fastforce intro: map_pmf_idI split: if_splits simp add: set_prod_pmf)

  finally show ?thesis by simp
qed

end

lemma prod_pmf_swap_uncurried :
  assumes \<open>finite I\<close> \<open>finite J\<close>
  shows
    \<open>map_pmf
      (\<lambda> \<omega>. \<lambda> (i, j) \<in> I \<times> J. \<omega> i j)
      (prod_pmf I (\<lambda> i. prod_pmf J (\<lambda> j. M (i, j)))) =
    map_pmf
      (\<lambda> \<omega>. \<lambda> (i, j) \<in> I \<times> J. \<omega> j i)
      (prod_pmf J (\<lambda> j. prod_pmf I (\<lambda> i. M (i, j))))\<close>
    (is \<open>?L = ?R\<close>)
proof -
  have \<open>?L = map_pmf
    (\<lambda> \<omega> (i, j). \<omega> (j, i))
    (prod_pmf (J \<times> I) (\<lambda> (i, j). M (j, i)))\<close>
    using assms by (metis prod_pmf_swap prod_pmf_uncurry)

  also have \<open>\<dots> = map_pmf
    (\<lambda> \<omega> (i, j). (\<lambda> (j, i) \<in> J \<times> I. \<omega> j i) (j, i))
    (prod_pmf J (\<lambda> i. prod_pmf I (\<lambda> j. M (j, i))))\<close>
    using assms by (simp add: prod_pmf_uncurry map_pmf_comp)

  also have \<open>\<dots> = ?R\<close> by (fastforce intro: map_pmf_cong)
  
  finally show ?thesis .
qed

subsubsection \<open>Properties about the Bernoulli and Binomial distributions\<close>

lemma bernoulli_pmf_0_1 [simp] :
  \<open>bernoulli_pmf 0 = return_pmf False\<close>
  \<open>bernoulli_pmf 1 = return_pmf True\<close>
  by (simp_all add: bernoulli_pmf.rep_eq pmf_eqI)

lemma
  binomial_pmf_p_0 [simp] : \<open>binomial_pmf n 0 = return_pmf 0\<close> and
  binomial_pmf_p_1 [simp] : \<open>binomial_pmf n 1 = return_pmf n\<close>
  using set_pmf_subset_singleton by fastforce+

context
  fixes p :: real
  assumes p [simp] : \<open>0 \<le> p\<close> \<open>p \<le> 1\<close>
begin

lemma bernoulli_pmf_eq_bernoulli_pmfs :
  assumes \<open>0 \<le> p'\<close> \<open>p' \<le> 1\<close>
  shows
    \<open>bernoulli_pmf (p * p') = do {
      b \<leftarrow> bernoulli_pmf p;
      b' \<leftarrow> bernoulli_pmf p';
      return_pmf <| b \<and> b' }\<close>
  using assms p
  apply (intro pmf_eqI)
  by (simp add: mult_le_one bernoulli_pmf.rep_eq pmf_bind algebra_simps)

lemmas bernoulli_pmf_eq_bernoulli_pmfs' = bernoulli_pmf_eq_bernoulli_pmfs[
  simplified map_pmf_def[symmetric]]

private lemma bernoulli_eq_map_Pi_pmf_aux : 
  assumes \<open>card I = Suc k\<close>
  shows
    \<open>bernoulli_pmf (p ^ Suc k) = (
      \<lblot>bernoulli_pmf p\<rblot>
        |> Pi_pmf I dflt
        |> map_pmf (Ball I))\<close>
    (is \<open>?L k = ?R I\<close>)
using assms proof (induction k arbitrary: I)
  case 0
  then show ?case
    by (auto simp add: Pi_pmf_singleton card_1_singleton_iff map_pmf_comp)
next
  case (Suc k)
  moreover from calculation obtain x J where
    \<open>finite J\<close> \<open>card J = Suc k\<close> \<open>I = insert x J\<close> \<open>x \<notin> J\<close>
    by (metis card_Suc_eq_finite)

  moreover from calculation have
    \<open>?L (Suc k)  = do {
      b \<leftarrow> bernoulli_pmf p;
      b' \<leftarrow> ?R J;
      return_pmf <| b \<and> b' }\<close>
    by (simp add: bernoulli_pmf_eq_bernoulli_pmfs mult_le_one power_le_one_iff)

  moreover from calculation
  have \<open>\<dots> = ?R (insert x J)\<close>
    apply (subst Pi_pmf_insert')
      by (auto
        intro: bind_pmf_cong map_pmf_cong
        simp flip: map_pmf_def
        simp add: map_pmf_comp map_bind_pmf)

  ultimately show ?case by simp
qed

text
  \<open>This says that to simulate a coin flip with the probability of getting H as
  $p ^ k$, we can flip $\ge k$ coins with probability $p$ of getting H, and
  check if any $k$ of them are H. 

  More precisely, a bernoulli RV with probability $p ^ k$ ($k > 0$) is equivalent
  to doing the following:
  \begin{enumerate}
    \item We fix a (finite) family of indices $J$, and a subset $I \subseteq J$
    of cardinality $k$.

    \item We construct a family of Bernoulli RVs of probability $p$,
     indexed by $J$, and sample from it.

     \item Viewing the outcome as a characteristic function of $J$, we check if
     the subset it defines contains $I$, outputting True iff that is the case.
  \end{enumerate}\<close>
lemma bernoulli_eq_map_Pi_pmf :
  assumes \<open>finite J\<close> \<open>card I > 0\<close> \<open>I \<subseteq> J\<close>
  shows
    \<open>bernoulli_pmf (p ^ card I) = (
      \<lblot>bernoulli_pmf p\<rblot>
        |> Pi_pmf J dflt
        |> map_pmf (Ball I))\<close>
  using
    assms p 
    bernoulli_eq_map_Pi_pmf_aux[of I \<open>card I - 1\<close> dflt]
    Pi_pmf_subset[of J I dflt \<open>\<lblot>bernoulli_pmf p\<rblot>\<close>]
  by (fastforce simp add: map_pmf_comp)

end

abbreviation bernoulli_nat_pmf :: \<open>real \<Rightarrow> nat pmf\<close> where
 \<open>bernoulli_nat_pmf \<equiv> bernoulli_pmf >>> map_pmf of_bool\<close>

context binomial_distribution
begin

abbreviation Pi_bernoulli_nat_pmf :: \<open>(nat \<Rightarrow> nat) pmf\<close> where
  \<open>Pi_bernoulli_nat_pmf \<equiv> Pi_pmf {..< n} 0 \<lblot>bernoulli_nat_pmf p\<rblot>\<close>

lemma binomial_pmf_eq_map_sum_of_bernoullis :
  \<open>binomial_pmf n p = (
    Pi_bernoulli_nat_pmf
      |> map_pmf (\<lambda> P. \<Sum> m < n. P m))\<close>
  (is \<open>?L = ?R\<close>)
proof -
  from p have \<open>?L = (
    prod_pmf {..< n} \<lblot>bernoulli_pmf p\<rblot>
      |> map_pmf (\<lambda> P. card {m. m < n \<and> P m}))\<close>
    apply (subst binomial_pmf_altdef'[where A = \<open>{..< n}\<close> and dflt = undefined])
      by simp_all

  also have \<open>\<dots> = ?R\<close>
    unfolding Pi_pmf_map'[OF finite_lessThan, where dflt' = undefined] map_pmf_comp
    by (fastforce simp add: Collect_conj_eq lessThan_def)

  finally show ?thesis .
qed

lemma expectation_binomial_pmf :
  \<open>measure_pmf.expectation (binomial_pmf n p) id = n * p\<close>
  using p
  by (simp add:
    binomial_pmf_eq_map_sum_of_bernoullis
    expectation_sum_Pi_pmf integrable_measure_pmf_finite)

end

subsubsection \<open>Bernoulli random matrices\<close>

definition bernoulli_matrix ::
  \<open>nat \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (nat \<times> nat \<Rightarrow> bool) pmf\<close> where
  \<open>bernoulli_matrix m n p \<equiv>
    prod_pmf ({..< m} \<times> {..< n}) \<lblot>bernoulli_pmf p\<rblot>\<close>

lemma bernoulli_matrix_eq_uncurry_prod :
  fixes m n
  defines \<open>m' \<equiv> {..< m}\<close> and \<open>n' \<equiv> {..< n}\<close>
  shows
    \<open>bernoulli_matrix m n p = (
      prod_pmf m' \<lblot>prod_pmf n' \<lblot>bernoulli_pmf p\<rblot>\<rblot>
        |> map_pmf (\<lambda> \<omega>. \<lambda> (x, y) \<in> m' \<times> n'. \<omega> x y))\<close>
  unfolding bernoulli_matrix_def m'_def n'_def
  by (simp add: prod_pmf_uncurry)

subsection \<open>foldM\_pmf and related Hoare rules\<close>

subsubsection \<open>foldM\_pmf\<close>

abbreviation \<open>foldM_pmf \<equiv> foldM bind_pmf return_pmf\<close>
abbreviation \<open>foldM_pmf_enumerate \<equiv> foldM_enumerate bind_pmf return_pmf\<close>

lemma foldM_pmf_snoc :
  "foldM_pmf f (xs @ [x]) val = bind_pmf (foldM_pmf f xs val) (f x)"
  apply (induction xs arbitrary:val)
    by (simp_all
      add: bind_return_pmf bind_return_pmf' bind_assoc_pmf
      cong: bind_pmf_cong)

subsubsection \<open>Hoare triple for Kleisli morphisms over PMF\<close>

abbreviation pmf_hoare_triple
  (\<open>\<turnstile>pmf \<lbrakk> _ \<rbrakk> _ \<lbrakk> _ \<rbrakk> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<equiv> (\<And> x. P x \<Longrightarrow> AE y in measure_pmf <| f x. Q y)\<close>

subsubsection \<open>Hoare rules for foldM\_pmf\<close>

context
  fixes
    P :: \<open>nat \<Rightarrow> 'b \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

private abbreviation (input)
  \<open>P' \<equiv> \<lambda> idx x val.
    (idx, x) \<in> set (List.enumerate offset xs) \<and>
    P idx val\<close>

lemma pmf_hoare_foldM_enumerate :
  assumes \<open>\<And> idx x. \<turnstile>pmf \<lbrakk>P' idx x\<rbrakk> f (idx, x) \<lbrakk>P (Suc idx)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf
    \<lbrakk>P offset\<rbrakk>
    foldM_pmf_enumerate f xs offset
    \<lbrakk>P (offset + length xs)\<rbrakk>\<close>
using assms proof (induction xs arbitrary: offset)
  case Nil
  then show ?case by (simp add: AE_measure_pmf_iff foldM_enumerate_def)
next
  case (Cons _ _)
  then show ?case
    apply (simp add: AE_measure_pmf_iff foldM_enumerate_def)
    by (metis add_Suc_right add_Suc_shift)
qed

lemma pmf_hoare_foldM_indexed' :
  assumes \<open>\<And> idx x. \<turnstile>pmf \<lbrakk>P' idx x\<rbrakk> f x \<lbrakk>P (Suc idx)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P offset\<rbrakk> foldM_pmf f xs \<lbrakk>P (offset + length xs)\<rbrakk>\<close>
  using assms pmf_hoare_foldM_enumerate
  by (metis foldM_eq_foldM_enumerate prod.sel(2))

end

lemmas pmf_hoare_foldM_indexed =
  pmf_hoare_foldM_indexed'[where offset = 0, simplified]

lemma pmf_hoare_foldM :
  assumes \<open>\<And> x. \<turnstile>pmf \<lbrakk>P\<rbrakk> f x \<lbrakk>P\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>P\<rbrakk> foldM_pmf f xs \<lbrakk>P\<rbrakk>\<close>
  using assms pmf_hoare_foldM_indexed[where P = \<open>\<lblot>P\<rblot>\<close>] by blast

subsection \<open>PMF relational Hoare rules\<close>

text
  \<open>This subsection defines a suitable notion of Hoare triples for the total
  correctness of Kleisli morphisms over \texttt{pmf}, and provides various
  proof rules for monadic folds.
  These are based on \texttt{pRHL} from \cite{barthe_hsu_2020}.\<close>

lemma rel_pmf_bindI1 :
  assumes \<open>\<And> x. x \<in> set_pmf p \<Longrightarrow> rel_pmf R (f x) q\<close>
  shows \<open>rel_pmf R (p \<bind> f) q\<close>
  using assms rel_spmf_bindI1 rel_spmf_spmf_of_pmf
  by (metis bind_spmf_of_pmf lossless_spmf_spmf_of_spmf set_spmf_spmf_of_pmf spmf_of_pmf_bind)

lemma rel_pmf_bindI2 :
  assumes \<open>\<And> x. x \<in> set_pmf q \<Longrightarrow> rel_pmf R p (f x)\<close>
  shows \<open>rel_pmf R p (q \<bind> f)\<close>
  using assms rel_spmf_bindI2 rel_spmf_spmf_of_pmf
  by (metis bind_spmf_of_pmf lossless_spmf_spmf_of_spmf set_spmf_spmf_of_pmf spmf_of_pmf_bind)

subsubsection \<open>Relational Hoare triple for Kleisli morphism over PMF\<close>

abbreviation pmf_rel_hoare_triple
  (\<open>\<turnstile>pmf \<lbrakk> _ \<rbrakk> \<langle> _ | _ \<rangle> \<lbrakk> _ \<rbrakk>\<close> [21, 20, 20, 21] 60) where
  \<open>(\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>S\<rbrakk>) \<equiv> (\<And> x x'. R x x' \<Longrightarrow> rel_pmf S (f x) (f' x'))\<close>

subsubsection \<open>One-sided Hoare skip rules\<close>

lemma rel_hoare_skip_left [simp] :
  \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f >>> return_pmf | f'\<rangle> \<lbrakk>S\<rbrakk> \<equiv> (\<And> x. \<turnstile>pmf \<lbrakk>R x\<rbrakk> f' \<lbrakk>S (f x)\<rbrakk>)\<close>
  by (simp add: AE_measure_pmf_iff rel_pmf_return_pmf1)

lemma rel_hoare_skip_right [simp] :
  \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f' >>> return_pmf\<rangle> \<lbrakk>S\<rbrakk> \<equiv>
    (\<And> x'. \<turnstile>pmf \<lbrakk>flip R x'\<rbrakk> f \<lbrakk>flip S (f' x')\<rbrakk>)\<close>
  apply standard by (simp_all add: AE_measure_pmf_iff rel_pmf_return_pmf2)

subsubsection \<open>Two-sided Hoare rules for foldM\_pmf\<close>

context
  fixes
    R :: \<open>nat \<Rightarrow> 'b \<Rightarrow>'c \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

private abbreviation (input)
  \<open>foldM_enumerate' \<equiv> \<lambda> f. foldM_pmf_enumerate f xs offset\<close>

private abbreviation (input)
  \<open>R' \<equiv> \<lambda> idx x val val'.
    (idx, x) \<in> set (List.enumerate offset xs) \<and>
    R idx val val'\<close>

lemma pmf_rel_hoare_foldM_enumerate :
  assumes \<open>\<And> index x.
    \<turnstile>pmf \<lbrakk>R' index x\<rbrakk> \<langle>f (index, x) | f' (index, x)\<rangle> \<lbrakk>R (Suc index)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf
    \<lbrakk>R offset\<rbrakk>
    \<langle>foldM_enumerate' f | foldM_enumerate' f'\<rangle>
    \<lbrakk>R (offset + length xs)\<rbrakk>\<close>
using assms proof (induction xs arbitrary: offset)
  case Nil
  then show ?case by (simp add: foldM_enumerate_def)
next
  case (Cons _ _)
  then show ?case
    apply (simp flip: add_Suc add: foldM_enumerate_def)
    by (blast intro: rel_pmf_bindI)
qed

lemma pmf_rel_hoare_foldM_indexed' :
  assumes \<open>\<And> idx x.
    \<turnstile>pmf \<lbrakk>R' idx x\<rbrakk> \<langle>f x | f' x\<rangle> \<lbrakk>R (Suc idx)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf
    \<lbrakk>R offset\<rbrakk>
    \<langle>foldM_pmf f xs | foldM_pmf f' xs\<rangle>
    \<lbrakk>R (offset + length xs)\<rbrakk>\<close>
  using assms pmf_rel_hoare_foldM_enumerate
  by (metis foldM_eq_foldM_enumerate prod.sel(2))

end

lemmas pmf_rel_hoare_foldM_indexed =
  pmf_rel_hoare_foldM_indexed'[where offset = 0, simplified]

lemma pmf_rel_hoare_foldM :
  assumes \<open>\<And> x. \<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f x | f' x\<rangle> \<lbrakk>R\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>foldM_pmf f xs | foldM_pmf f' xs\<rangle> \<lbrakk>R\<rbrakk>\<close>
  using assms pmf_rel_hoare_foldM_indexed[where R = \<open>\<lblot>R\<rblot>\<close>] by blast

end