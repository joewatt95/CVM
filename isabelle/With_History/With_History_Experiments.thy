theory With_History_Experiments

imports
  CVM.Basic_Algo

begin

context basic_algo
begin

definition least_index :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> nat option\<close> where
  \<open>least_index xs x \<equiv>
    if x \<in> set xs
    then Some <| LEAST index. xs ! index = x
    else None\<close>

lemma least_index_le_length :
  assumes \<open>least_index xs x = Some index\<close>
  shows \<open>index < length xs\<close> 

  by (metis (mono_tags, lifting) assms in_set_conv_nth least_index_def linorder_less_linear not_less_Least option.discI option.inject order_less_trans)

lemma least_index_inj_on :
  \<open>inj_on (least_index xs) (set xs)\<close>

  by (smt (verit) LeastI basic_algo.least_index_def in_set_conv_nth inj_onI option.simps(1))

(* abbreviation is_some where
  \<open>is_some x \<equiv> \<not> Option.is_none x\<close> *)

lemma
  assumes
    \<open>chi \<subseteq> set xs\<close>
  defines
    \<open>lhs \<equiv> (
      \<lblot>bernoulli_pmf <| 1 / 2\<rblot>
        |> Pi_pmf chi False
        |> map_pmf (flip Set.filter chi))\<close> and

    \<open>rhs indices \<equiv> (
      \<lblot>bernoulli_pmf <| 1 / 2\<rblot>
        |> Pi_pmf indices False
        |> map_pmf
            (\<lambda> keep_index.
              {x \<in> chi. x
                |> least_index xs
                |> Option.case_option False keep_index}))\<close> and

    \<open>indices \<equiv> {0 ..< length xs}\<close>

  shows \<open>lhs = rhs indices\<close>
proof -
  let ?least_indices_in_chi =
    \<open>{index. \<exists> x \<in> chi. least_index xs x = Some index}\<close>

  let ?lookup_indices_in_xs = \<open>(`) <| (!) xs\<close>

  let ?lhs = \<open>Pow chi |> pmf_of_set\<close>
  let ?rhs =
    \<open>Pow ?least_indices_in_chi
      |> pmf_of_set
      |> map_pmf ?lookup_indices_in_xs\<close>

  have \<open>lhs = ?lhs\<close>
    using assms
    by (simp add: Set.filter_def finite_subset pmf_of_set_Pow_conv_bernoulli)

  moreover have \<open>rhs indices = ?rhs\<close>
  proof -
    have \<open>rhs indices = rhs ?least_indices_in_chi\<close>
      using assms
      apply simp
      apply (subst
        Pi_pmf_subset[where ?A' = ?least_indices_in_chi, where ?A = indices])
      apply simp
      using indices_def least_index_le_length apply fastforce
      apply (simp add: map_pmf_comp) apply (intro map_pmf_cong) apply simp
      by (smt (verit) Collect_cong assms(1) basic_algo.least_index_def option.simps(5) subset_eq) 

    also have
      \<open>... = (
        \<lblot>bernoulli_pmf <| 1 / 2\<rblot>
          |> Pi_pmf ?least_indices_in_chi False 
          |> map_pmf
              (\<lambda> keep_index. {index \<in> ?least_indices_in_chi. keep_index index})
          |> map_pmf ?lookup_indices_in_xs)\<close>
      unfolding assms
      apply (simp add: map_pmf_comp) apply (intro map_pmf_cong) apply blast
      apply (simp add: image_def least_index_def)
      apply (subst (asm) set_Pi_pmf)
      apply simp apply (smt (z3) Least_le bounded_nat_set_is_finite in_set_conv_nth mem_Collect_eq order_le_less_trans)
      apply (intro set_eqI) by (smt (verit) LeastI_ex in_set_conv_nth mem_Collect_eq)

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

lemma
  \<open>replicate_pmf n p = (
    \<lblot>p\<rblot>
      |> Pi_pmf {offset ..< n + offset} dflt
      |> map_pmf (flip map [offset ..< n + offset]))\<close>
proof (induction n arbitrary: offset)
  case 0
  then show ?case by simp
next
  case (Suc n)

  have * : \<open>\<And> offset n.
    {offset ..< Suc n + offset} = insert offset {Suc offset ..< Suc n + offset}\<close>
    by fastforce

  have ** : \<open>\<And> offset f.
    1 \<le> n
    \<Longrightarrow> map f [offset ..< n + offset] = f offset # map f [Suc offset ..< n + offset]\<close>
    apply (induction n) by (simp_all add: not_less_eq_eq)

  show ?case
    apply (subst *) apply (subst Pi_pmf_insert')
    by (simp_all
        add:
          Suc[of \<open>Suc offset\<close>] **
          map_bind_pmf map_pmf_def[symmetric] map_pmf_comp set_Pi_pmf)
qed

end

end