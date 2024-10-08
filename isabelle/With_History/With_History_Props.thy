theory With_History_Props

imports
  CVM.With_History_Algo

begin

sledgehammer_params [
  (* verbose *)
  minimize = true,
  preplay_timeout = 15,
  timeout = 60,
  max_facts = smart,
  provers = "
    cvc4 z3 verit
    e vampire spass
  "
]

context with_history
begin

lemma bernoulli_pmf_eq_flip_and_record :
  \<open>bernoulli_pmf p = (
    state
      |> flip_coins_and_record 1 p
      |> map_pmf (\<lambda> (coin_flips, _). coin_flips 0))\<close>

  by (simp add:
    flip_coins_and_record_def
    map_bind_pmf map_pmf_def[symmetric] map_pmf_comp
    Pi_pmf_singleton Let_def)

lemma filter_Pi_pmf_eq_flip_and_record_and_filter :
  fixes xs chi state start_index
  assumes \<open>chi \<subseteq> set xs\<close>
  defines
    \<open>lhs \<equiv> (
      \<lblot>bernoulli_pmf <| 1 / 2\<rblot>
        |> Pi_pmf chi False
        |> map_pmf (flip Set.filter chi))\<close> and

    \<open>rhs \<equiv> (
      let filter_chi_with = \<lambda> coin_flips. (
        {x \<in> chi. coin_flips (the <| least_index xs x)})
      in (state
        |> flip_coins_and_record (length xs) (1 / 2)
        |> map_pmf (\<lambda> (coin_flips, _). filter_chi_with coin_flips)))\<close>
    (is \<open>_ \<equiv> let _ = ?filter_chi_with in _\<close>)

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
          |> map_pmf ?filter_chi_with)\<close>
        apply (simp add:
          assms flip_coins_and_record_def Let_def
          map_bind_pmf map_pmf_def[symmetric] map_pmf_comp)
        apply (subst Pi_pmf_subset[of ?indices_in_xs ?least_indices_in_chi])
        using \<open>chi \<subseteq> set xs\<close> by (auto
          intro!: least_index_le_length
          intro: map_pmf_cong
          simp add: least_index_def map_pmf_comp)

    also have
      \<open>... = (
        \<lblot>bernoulli_pmf <| 1 / 2\<rblot>
          |> Pi_pmf ?least_indices_in_chi False 
          |> map_pmf
              (\<lambda> coin_flips. {index \<in> ?least_indices_in_chi. coin_flips index})
          |> map_pmf ?lookup_indices_in_xs)\<close>
      apply (simp add: map_pmf_comp image_def least_index_def)
      apply (intro map_pmf_cong) apply blast
      apply (intro set_eqI)
      by (smt (verit, best) \<open>chi \<subseteq> set xs\<close> LeastI_ex in_mono mem_Collect_eq set_conv_nth)

    also have \<open>... = ?rhs\<close>
    proof -
      have \<open>finite ?least_indices_in_chi\<close>
        by (smt (z3) bounded_nat_set_is_finite least_index_le_length mem_Collect_eq) 
      then show ?thesis using pmf_of_set_Pow_conv_bernoulli by fastforce
    qed

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

    have \<open>finite ?least_indices_in_chi\<close>
      by (smt (z3) bounded_nat_set_is_finite least_index_le_length mem_Collect_eq) 

    show ?thesis
      apply (simp add: bij_betw_iff_bijections)
      apply (intro exI[where ?x = ?least_indices_of_elems])
      apply (auto simp add: image_def least_index_def in_these_eq)
      apply (smt (verit, ccfv_SIG) LeastI_ex in_set_conv_nth mem_Collect_eq subset_eq)
      apply (smt (verit, best) LeastI dual_order.antisym in_mono in_set_conv_nth linorder_not_le mem_Collect_eq not_less_Least) 
      apply (smt (verit, del_insts) IntI LeastI in_set_conv_nth mem_Collect_eq subsetD) 
      apply blast
      apply (smt (verit, best) LeastI mem_Collect_eq set_conv_nth)
      by (smt (verit, ccfv_SIG) Collect_empty_eq Int_Un_eq(2) LeastI_ex assms(1) in_these_eq inf_bot_left le_iff_inf mem_Collect_eq order_trans set_conv_nth subsetD sup_commute)
  qed

  ultimately show ?thesis by metis
qed

end

end