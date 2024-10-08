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
  fixes xs chi state
  assumes \<open>chi \<subseteq> set xs\<close>
  defines
    \<open>lhs \<equiv> (
      \<lblot>bernoulli_pmf <| 1 / 2\<rblot>
        |> Pi_pmf chi False
        |> map_pmf (flip Set.filter chi))\<close> and

    \<open>rhs \<equiv> (
      state
        |> flip_coins_and_record (length xs) (1 / 2)
        |> map_pmf (
            \<lambda> (coin_flips, _).
              {x \<in> chi. coin_flips <| the <| least_index xs x}))\<close>
    (is \<open>_ \<equiv> (_ |> _ |> map_pmf (\<lambda> (x, _). ?filter_chi_with x))\<close>)

  shows \<open>lhs = rhs\<close>
proof -
  let ?least_indices_in_chi =
    \<open>{index. \<exists> x \<in> chi. least_index xs x = Some index}\<close>
  let ?lookup_indices_in_xs = \<open>(`) <| (!) xs\<close>

  have
    \<open>bij_betw ?lookup_indices_in_xs
      (Pow ?least_indices_in_chi) (Pow chi)\<close>
    apply (intro bij_betw_byWitness[where ?f' = \<open>Option.these <<< (`) (least_index xs)\<close>])
    apply (simp_all add: image_def least_index_def subset_eq set_eq_iff Int_def Un_def)
    by (smt (verit, ccfv_SIG) \<open>chi \<subseteq> set xs\<close> in_these_eq LeastI_ex in_set_conv_nth mem_Collect_eq PowD option.exhaust option.inject subsetD)+

  then have
    \<open>lhs = (
      Pow ?least_indices_in_chi
        |> pmf_of_set
        |> map_pmf ?lookup_indices_in_xs)\<close>
    using assms bij_betw_finite finite_subset map_pmf_of_set_bij_betw
    by (fastforce simp add: Set.filter_def pmf_of_set_Pow_conv_bernoulli)

  also have
    \<open>... = (
      \<lblot>bernoulli_pmf <| 1 / 2\<rblot>
        |> Pi_pmf ?least_indices_in_chi False
        |> map_pmf ?filter_chi_with)\<close>
    apply (subst pmf_of_set_Pow_conv_bernoulli[symmetric])
    apply (smt (z3) bounded_nat_set_is_finite least_index_le_length mem_Collect_eq) 
    apply (simp add: map_pmf_comp image_def least_index_def)
    apply (intro map_pmf_cong) apply blast apply (intro set_eqI)
    by (smt (verit, ccfv_SIG) \<open>chi \<subseteq> set xs\<close> in_these_eq LeastI_ex in_set_conv_nth mem_Collect_eq PowD option.exhaust option.inject subsetD)

  finally show ?thesis
    apply (simp add:
      assms flip_coins_and_record_def Let_def
      map_bind_pmf map_pmf_def[symmetric] map_pmf_comp)
    apply (subst Pi_pmf_subset[of \<open>{0 ..< length xs}\<close> ?least_indices_in_chi])
    using \<open>chi \<subseteq> set xs\<close> by (auto
      intro!: least_index_le_length intro: map_pmf_cong
      simp add: least_index_def map_pmf_comp)
qed

end

end