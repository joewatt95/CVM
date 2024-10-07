theory With_History_Props

imports
  CVM.With_History_Algo

begin

context with_history
begin

lemma
  fixes p f state start_index
  defines
    \<open>lhs \<equiv> (bernoulli_pmf p |> map_pmf f)\<close> and

    \<open>rhs \<equiv> (
      state
        |> flip_coins_and_record start_index 1 p
        |> map_pmf (\<lambda> (coin_flips, _). f (coin_flips 0)))\<close>

  shows \<open>lhs = rhs\<close>

  by (simp
      add:
        assms flip_coins_and_record_def
        map_bind_pmf map_pmf_def[symmetric] map_pmf_comp
        Pi_pmf_singleton Let_def)

lemma
  fixes xs chi state start_index
  assumes \<open>chi \<subseteq> set xs\<close>
  defines
    \<open>lhs \<equiv> (
      \<lblot>bernoulli_pmf <| 1 / 2\<rblot>
        |> Pi_pmf chi False
        |> map_pmf (flip Set.filter chi))\<close> and

    \<open>rhs \<equiv> (
      state
        |> flip_coins_and_record start_index (length xs) (1 / 2)
        |> map_pmf
            (fst >>> (\<lambda> coin_flips.
              {x \<in> chi. x
                |> least_index xs
                |> Option.case_option False coin_flips})))\<close>
    (is \<open>_ \<equiv> (state |> _ |> map_pmf (fst >>> ?filter_chi))\<close>)

  shows \<open>lhs = rhs\<close>
proof -
  let ?least_indices_in_chi =
    \<open>{index. \<exists> x \<in> chi. least_index xs x = Some index}\<close>

  let ?lookup_indices_in_xs = \<open>(`) <| (!) xs\<close>

  let ?lhs = \<open>Pow chi |> pmf_of_set\<close>
  let ?rhs =
    \<open>Pow ?least_indices_in_chi
      |> pmf_of_set
      |> map_pmf ?lookup_indices_in_xs\<close>

  let ?indices_in_xs = \<open>{0 ..< length xs}\<close>

  have \<open>lhs = ?lhs\<close>
    using assms
    by (simp add: Set.filter_def finite_subset pmf_of_set_Pow_conv_bernoulli)

  moreover have \<open>rhs = ?rhs\<close>
  proof -
    have
      \<open>rhs = (
        \<lblot>bernoulli_pmf <| 1 / 2\<rblot>
          |> Pi_pmf ?least_indices_in_chi False
          |> map_pmf ?filter_chi)\<close>
      apply (simp
        add:
          assms flip_coins_and_record_def Let_def
          map_bind_pmf map_pmf_def[symmetric] map_pmf_comp)
      apply (subst
        Pi_pmf_subset[
          where ?A' = ?least_indices_in_chi,
          where ?A = ?indices_in_xs])
      apply simp
      using least_index_le_length apply fastforce
      by (auto
          intro: map_pmf_cong
          simp add: least_index_def map_pmf_comp)

    also have
      \<open>... = (
        \<lblot>bernoulli_pmf <| 1 / 2\<rblot>
          |> Pi_pmf ?least_indices_in_chi False 
          |> map_pmf
              (\<lambda> coin_flips. {index \<in> ?least_indices_in_chi. coin_flips index})
          |> map_pmf ?lookup_indices_in_xs)\<close>
      unfolding assms
      apply (simp add: map_pmf_comp) apply (intro map_pmf_cong) apply blast
      apply (simp add: image_def)
      apply (subst (asm) set_Pi_pmf)
      apply simp apply (smt (z3) bounded_nat_set_is_finite least_index_le_length mem_Collect_eq) 
      apply (intro set_eqI)
      apply (simp add: least_index_def)
       by (smt (verit, ccfv_SIG) LeastI_ex in_set_conv_nth) 

    also have
      \<open>... = ?rhs\<close>
      apply (intro map_pmf_cong)
      apply (subst pmf_of_set_Pow_conv_bernoulli)
      apply (smt (z3) bounded_nat_set_is_finite least_index_le_length mem_Collect_eq) 
      by auto

    finally show ?thesis by blast
  qed

  moreover have \<open>?lhs = ?rhs\<close>
  proof -
    show ?thesis when
      \<open>bij_betw ?lookup_indices_in_xs (Pow ?least_indices_in_chi) <| Pow chi\<close>
      (is ?thesis)
      using assms that bij_betw_finite finite_subset
      apply (intro map_pmf_of_set_bij_betw[symmetric])
      apply blast apply blast by blast

    let ?least_indices_of_elems =
      \<open>Option.these <<< (`) (least_index xs)\<close>

    show ?thesis
      apply (simp add: bij_betw_iff_bijections)
      apply (intro exI[where ?x = ?least_indices_of_elems])
      sorry
  qed

  ultimately show ?thesis by metis
qed

end

end