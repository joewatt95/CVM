theory Distinct_Elems_Algo_Transforms_Binomial

imports
  Distinct_Elems_Algo_Transforms_Nondet

begin

context with_threshold_pos
begin

lemma map_pmf_nondet_alg_aux_eq:
  assumes \<open>length xs \<le> n\<close> \<open>k \<le> m\<close>
  shows
    \<open>map_pmf (nondet_alg_aux k xs)
      (fair_bernoulli_matrix m n) =
    map_pmf (\<lambda> P. {y \<in> set xs. P y})
      (prod_pmf (set xs) \<lblot>bernoulli_pmf <| 1 / 2 ^ k\<rblot>)\<close>
    (is \<open>?L = _\<close>)
proof -
  have \<open>?L =
    map_pmf
    (\<lambda> \<phi>. nondet_alg_aux k xs (\<lambda> (x, y) \<in> {..< m} \<times> {..< n}. \<phi> y x))
    (prod_pmf {..< n} \<lblot>prod_pmf {..< m} \<lblot>coin_pmf\<rblot>\<rblot>)\<close>
    (is \<open>_ = map_pmf ?go _\<close>)
    by (simp add: bernoulli_matrix_eq_uncurry_prod map_pmf_comp)

  also have \<open>\<dots> =
    map_pmf (\<lambda> f. {y \<in> set xs. \<forall> k' < k. f y k'})
    (prod_pmf (set xs) \<lblot>prod_pmf {..< m} \<lblot>coin_pmf\<rblot>\<rblot>)\<close>
    proof -
      have
        \<open>map_pmf ?go =
          map_pmf (\<lambda> f. {x \<in> set xs. \<forall> k' < k. f x k'}) \<circ>
          map_pmf (\<lambda> f. \<lambda> i \<in> set xs. f (find_last i xs))\<close>
        using assms
        by (auto
          intro!: map_pmf_cong
          simp flip: map_pmf_compose
          simp add:
            nondet_alg_aux_def fun_eq_iff dual_order.strict_trans1
            find_last_correct_1(2))

      then show ?thesis
        using assms find_last_inj
        apply (simp add: map_pmf_compose)
        apply (subst prod_pmf_reindex)
        by (auto simp add: image_def find_last_eq_Max in_set_conv_nth)
    qed

  also have \<open>\<dots> =
    map_pmf
      (\<lambda> f. {y \<in> set xs. f y})
      (prod_pmf (set xs)
        \<lblot>map_pmf (\<lambda> f. \<forall> k' < k. f k') (prod_pmf {..< m} \<lblot>coin_pmf\<rblot>)\<rblot>)\<close>
    by (auto
      intro: map_pmf_cong
      simp add: Pi_pmf_map'[where dflt' = undefined] map_pmf_comp)

  finally show ?thesis
    using
      assms(2)          
      bernoulli_eq_map_Pi_pmf[where I = \<open>{.. k - 1}\<close>, unfolded Ball_def]
    by (cases k; simp add:
      power_one_over le_simps(2) map_pmf_comp Iic_subset_Iio_iff)
qed

theorem map_pmf_nondet_alg_eq_binomial :
  assumes \<open>length xs \<le> n\<close> \<open>k \<le> m\<close>
  shows
    \<open>map_pmf (nondet_alg k xs) (fair_bernoulli_matrix m n) =
    binomial_pmf (card <| set xs) (1 / 2 ^ k)\<close>
proof -
  let ?go = \<open>\<lambda> f. map_pmf (f k xs) (fair_bernoulli_matrix m n)\<close>

  have \<open>?go nondet_alg = map_pmf card (?go nondet_alg_aux)\<close>
    by (simp add: nondet_alg_def map_pmf_comp)

  then show ?thesis
    using binomial_pmf_altdef'[of \<open>set xs\<close>]
    by (simp add: assms map_pmf_nondet_alg_aux_eq map_pmf_comp)
qed

end

end