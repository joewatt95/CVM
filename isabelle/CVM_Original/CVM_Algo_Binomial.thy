theory CVM_Algo_Binomial

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Utils_Approx_Algo
  CVM_Algo_Lazy_Eager

begin

(* After processing the list xs, the chi is the set of
     distinct elements x in xs where the last time
     we flipped coins for x, the first k elements were heads. *)
definition nondet_alg_aux ::
  \<open>nat \<Rightarrow> 'a list \<Rightarrow> coin_matrix \<Rightarrow> 'a set\<close> where
  \<open>nondet_alg_aux \<equiv> \<lambda> k xs \<phi>.
    {x \<in> set xs. \<forall> k' < k. curry \<phi> k' (last_index xs x)}\<close>

abbreviation \<open>nondet_alg \<equiv> \<lambda> k xs. card <<< nondet_alg_aux k xs\<close>

definition state_inv ::
  \<open>'a list \<Rightarrow> coin_matrix \<Rightarrow> 'a state \<Rightarrow> bool\<close> where
  \<open>state_inv \<equiv> \<lambda> xs \<phi> state.
    state_chi state = nondet_alg_aux (state_k state) xs \<phi>\<close>

lemmas state_inv_def' =
  state_inv_def[simplified nondet_alg_aux_def set_eq_iff, simplified]

context cvm_algo_assms
begin

lemma step_1_eager_inv :
  assumes
    \<open>i < length xs\<close>
    \<open>state_inv (take i xs) \<phi> state\<close>
  shows
    \<open>state_inv (take (Suc i) xs) \<phi> (run_reader (step_1_eager xs i state) \<phi>)\<close>
  using assms
  unfolding step_1_eager_def' state_inv_def'
  by (simp add: run_reader_simps take_Suc_conv_app_nth)

lemma step_2_eager_inv :
  assumes
    \<open>i < length xs\<close>
    \<open>state_inv (take (Suc i) xs) \<phi> state\<close>
  shows \<open>state_inv (take (Suc i) xs) \<phi> (run_reader (step_2_eager xs i state) \<phi>)\<close>
  using assms
  unfolding step_2_eager_def' state_inv_def' last_index_up_to_def
  apply (simp add: run_reader_simps)
  by (smt (z3) dual_order.strict_trans1 last_index_less_size_conv length_take less_Suc_eq min_def not_less_simps(2))

lemma step_eager_inv :
  assumes
    \<open>i < length xs\<close>
    \<open>state_inv (take i xs) \<phi> state\<close>
  shows \<open>state_inv (take (Suc i) xs) \<phi> (run_reader (step_eager xs i state) \<phi>)\<close>
  unfolding step_eager_def
  using assms step_1_eager_inv step_2_eager_inv 
  by (fastforce simp add: run_reader_simps)

theorem eager_algorithm_inv :
  \<open>state_inv xs \<phi> <| run_reader (run_steps_eager xs initial_state) \<phi>\<close>
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case
    unfolding state_inv_def' initial_state_def
    by (simp add: run_reader_simps)
next
  case (snoc _ _)
  with step_eager_inv show ?case
    by (smt (verit, del_insts) append_eq_append_conv_if append_eq_conv_conj length_append_singleton lessI run_reader_simps(3) run_steps_eager_snoc)
qed

(* lemma nondet_measureD :
  assumes \<open>\<And> \<phi>. state_inv xs \<phi> (run_reader m \<phi>)\<close>
  shows
    \<open>\<P>(state in map_pmf (run_reader m) p.
      state_k state = k \<and> P (state_chi state))
    \<le> \<P>(chi in map_pmf (nondet_alg_aux k xs) p. P chi)\<close>
  apply simp
  by (metis (mono_tags, lifting) assms state_inv_def mem_Collect_eq pmf_mono) *)

context
  fixes xs and m n k :: nat
  assumes assms : \<open>length xs \<le> n\<close> \<open>k \<le> m\<close>
begin

lemma map_pmf_nondet_alg_aux_eq :
  \<open>map_pmf (nondet_alg_aux k xs)
    (bernoulli_matrix m n f) =
  map_pmf (\<lambda> P. {y \<in> set xs. P y})
    (prod_pmf (set xs) \<lblot>bernoulli_pmf <| f ^ k\<rblot>)\<close>
  (is \<open>?L = ?R\<close>)
proof -
  have \<open>?L =
    map_pmf
    (\<lambda> \<phi>. nondet_alg_aux k xs (\<lambda> (x, y) \<in> {..< m} \<times> {..< n}. \<phi> y x))
    (prod_pmf {..< n} \<lblot>prod_pmf {..< m} \<lblot>coin_pmf\<rblot>\<rblot>)\<close>
    (is \<open>_ = map_pmf ?go _\<close>)
    by (simp add: bernoulli_matrix_eq_uncurry_prod' map_pmf_comp)

  also have \<open>\<dots> =
    map_pmf (\<lambda> f. {y \<in> set xs. \<forall> k' < k. f y k'})
    (prod_pmf (set xs) \<lblot>prod_pmf {..< m} \<lblot>coin_pmf\<rblot>\<rblot>)\<close>
    proof -
      have
        \<open>map_pmf ?go =
          map_pmf (\<lambda> f. {x \<in> set xs. \<forall> k' < k. f x k'}) \<circ>
          map_pmf (\<lambda> f. \<lambda> x \<in> set xs. f (last_index xs x))\<close>
        using assms
        unfolding nondet_alg_aux_def map_pmf_compose[symmetric]
        apply (intro ext map_pmf_cong refl)
        by auto

      with assms show ?thesis
        apply simp
        apply (subst prod_pmf_reindex)
        using inj_on_last_index by auto
    qed

  also have \<open>\<dots> =
    map_pmf
      (\<lambda> f. {y \<in> set xs. f y})
      (prod_pmf (set xs)
        \<lblot>map_pmf (\<lambda> f. \<forall> k' < k. f k') (prod_pmf {..< m} \<lblot>coin_pmf\<rblot>)\<rblot>)\<close>
    by (auto
      intro: map_pmf_cong
      simp add: Pi_pmf_map'[where dflt' = undefined] map_pmf_comp)

  also from assms f bernoulli_eq_map_Pi_pmf[where I = \<open>{..< k}\<close>, unfolded Ball_def]
  have \<open>\<dots> = ?R\<close>
    apply (intro map_pmf_cong arg_cong2[where f = prod_pmf] refl ext)
    apply (cases k)
    by simp_all
    
  finally show ?thesis .
qed

theorem map_pmf_nondet_alg_eq_binomial :
  \<open>map_pmf (nondet_alg k xs) (bernoulli_matrix m n f) =
    binomial_pmf (card <| set xs) (f ^ k)\<close>
proof -
  let ?go = \<open>\<lambda> g. map_pmf (g k xs) (bernoulli_matrix m n f)\<close>

  have \<open>?go nondet_alg = map_pmf card (?go nondet_alg_aux)\<close>
    by (simp add: map_pmf_comp)

  with assms f
  show ?thesis
    apply (subst binomial_pmf_altdef')
    by (simp_all add: map_pmf_nondet_alg_aux_eq power_le_one map_pmf_comp)
qed

end

end

end