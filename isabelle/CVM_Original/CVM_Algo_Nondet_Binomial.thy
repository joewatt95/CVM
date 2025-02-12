theory CVM_Algo_Nondet_Binomial

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Utils_Approx_Algo
  CVM_Algo_Lazy_Eager

begin

definition nondet_algo ::
  \<open>nat \<Rightarrow> 'a list \<Rightarrow> coin_matrix \<Rightarrow> 'a set\<close> where
  \<open>nondet_algo \<equiv> \<lambda> k xs \<phi>.
    {x \<in> set xs. \<forall> k' < k. curry \<phi> k' (last_index xs x)}\<close>

definition state_inv ::
  \<open>'a list \<Rightarrow> coin_matrix \<Rightarrow> 'a state \<Rightarrow> bool\<close> where
  \<open>state_inv \<equiv> \<lambda> xs \<phi> state.
    state_chi state = nondet_algo (state_k state) xs \<phi>\<close>

lemmas state_inv_def' =
  state_inv_def[simplified nondet_algo_def set_eq_iff, simplified]

context cvm_algo_assms
begin

lemma step_1_eager_inv :
  assumes \<open>i < length xs\<close> \<open>state_inv (take i xs) \<phi> state\<close>
  shows \<open>state_inv (take (Suc i) xs) \<phi> (run_reader (step_1_eager xs i state) \<phi>)\<close>
  using assms
  unfolding step_1_eager_def' state_inv_def'
  by (simp add:take_Suc_conv_app_nth)

lemma step_2_eager_inv :
  assumes \<open>i < length xs\<close> \<open>state_inv (take (Suc i) xs) \<phi> state\<close>
  shows \<open>state_inv (take (Suc i) xs) \<phi> (run_reader (step_2_eager xs i state) \<phi>)\<close>
  using assms
  unfolding step_2_eager_def' state_inv_def' last_index_up_to_def
  apply simp
  by (smt (z3) last_index_less_size_conv length_take less_Suc_eq min_def min_less_iff_conj not_less_simps(2))

lemma step_eager_inv :
  assumes \<open>i < length xs\<close> \<open>state_inv (take i xs) \<phi> state\<close>
  shows \<open>state_inv (take (Suc i) xs) \<phi> (run_reader (step_eager xs i state) \<phi>)\<close>
  unfolding step_eager_def
  using assms step_1_eager_inv step_2_eager_inv 
  by fastforce

lemma eager_algo_inv :
  \<open>state_inv xs \<phi> <| run_reader (run_steps_eager xs initial_state) \<phi>\<close>
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case
    unfolding state_inv_def' initial_state_def
    by simp
next
  case (snoc _ _)
  with step_eager_inv show ?case
    by (smt (verit, del_insts) append_eq_append_conv_if append_eq_conv_conj length_append_singleton lessI run_reader_simps(3) run_steps_eager_snoc)
qed

theorem prob_eager_algo_le_nondet_algo_aux :
  \<open>\<P>(bool_matrix in measure_pmf rand_bool_matrix.
    let state = run_reader (run_steps_eager xs initial_state) bool_matrix
    in state_k state = k \<and> P (state_chi state))
  \<le> \<P>(bool_matrix in measure_pmf rand_bool_matrix.
      P (nondet_algo k xs bool_matrix))\<close>
  by (smt (verit, ccfv_SIG) eager_algo_inv mem_Collect_eq pmf_mono state_inv_def)

context
  fixes xs and m n k :: nat
  assumes assms : \<open>length xs \<le> n\<close> \<open>k \<le> m\<close>
begin

lemma map_pmf_nondet_algo_eq :
  \<open>map_pmf (nondet_algo k xs)
    (bernoulli_matrix m n f) =
  map_pmf (\<lambda> P. {x \<in> set xs. P x})
    (prod_pmf (set xs) \<lblot>bernoulli_pmf <| f ^ k\<rblot>)\<close>
  (is \<open>?L = ?R\<close>)
proof -
  let ?m' = \<open>{..< m}\<close> let ?n' = \<open>{..< n}\<close>
  let ?M = \<open>\<lambda> I. prod_pmf I \<lblot>prod_pmf {..< m} \<lblot>coin_pmf\<rblot>\<rblot>\<close>

  have \<open>?L =
    map_pmf
      (\<lambda> \<phi>. nondet_algo k xs (\<lambda> (x, y) \<in> ?m' \<times> ?n'. \<phi> y x))
      (?M ?n')\<close>
    unfolding bernoulli_matrix_eq_uncurry_prod
    apply (subst prod_pmf_swap_uncurried)
    by (simp_all add: map_pmf_comp)

  also have \<open>\<dots> = (
    ?M ?n' 
      |> map_pmf (\<lambda> P. \<lambda> x \<in> set xs. P (last_index xs x))
      |> map_pmf (\<lambda> P. {x \<in> set xs. \<forall> k' < k. P x k'}))\<close>
    unfolding nondet_algo_def map_pmf_comp
    using assms by (fastforce intro: map_pmf_cong)

  also have \<open>\<dots> =
    map_pmf
      (\<lambda> P. {x \<in> set xs. \<forall> k' < k. P x k'})
      (?M (set xs))\<close>
    apply (subst prod_pmf_reindex)
    using assms inj_on_last_index by auto

  also have \<open>\<dots> =
    map_pmf
      (\<lambda> P. {y \<in> set xs. P y})
      (prod_pmf (set xs)
        \<lblot>map_pmf (\<lambda> f. \<forall> k' < k. f k') (prod_pmf {..< m} \<lblot>coin_pmf\<rblot>)\<rblot>)\<close>
    apply (subst Pi_pmf_map'[OF finite_set])
    unfolding map_pmf_comp
    by (auto intro: map_pmf_cong)

  also from assms bernoulli_eq_map_Pi_pmf[where I = \<open>{..< k}\<close>, unfolded Ball_def]
  have \<open>\<dots> = ?R\<close>
    apply (intro map_pmf_cong arg_cong2[where f = prod_pmf] refl)
    apply (cases k)
    by simp_all

  finally show ?thesis .
qed

theorem map_pmf_nondet_algo_eq_binomial :
  \<open>map_pmf (card <<< nondet_algo k xs) (bernoulli_matrix m n f) =
    binomial_pmf (card <| set xs) (f ^ k)\<close>
  (is \<open>map_pmf (?card_nondet_algo _ _) _ = _\<close>)
proof -
  let ?go = \<open>\<lambda> g. map_pmf (g k xs) (bernoulli_matrix m n f)\<close>

  have \<open>?go ?card_nondet_algo = map_pmf card (?go nondet_algo)\<close>
    by (simp add: map_pmf_comp)

  with assms  show ?thesis
    apply (subst binomial_pmf_altdef')
    by (simp_all add: map_pmf_nondet_algo_eq power_le_one map_pmf_comp)
qed

corollary prob_eager_algo_le_binomial :
  \<open>\<P>(bool_matrix in bernoulli_matrix m n f.
    let state = run_reader (run_steps_eager xs initial_state) bool_matrix
    in state_k state = k \<and> P (card <| state_chi state))
  \<le> \<P>(estimate in binomial_pmf (card <| set xs) <| f ^ k. P estimate)\<close>
  using prob_eager_algo_le_nondet_algo_aux
  by (simp flip: map_pmf_nondet_algo_eq_binomial)

end

end

end