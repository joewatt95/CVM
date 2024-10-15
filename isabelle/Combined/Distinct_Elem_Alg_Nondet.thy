theory Distinct_Elem_Alg_Nondet
  imports
    CVM.Reader_Monad
    CVM.Lazify
    CVM.Utils_List
    Distinct_Elem_Alg_Eager
    "Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF"
begin

lemma find_last_before_self_eq:
  assumes "i < length xs"
  shows "find_last_before i (xs ! i) xs = i"
  unfolding find_last_before_def find_last_def Let_def
  using assms by auto

definition nondet_alg_aux :: "nat \<Rightarrow> 'a list \<Rightarrow> coin_matrix \<Rightarrow> 'a set"
  where "nondet_alg_aux k xs \<phi> =
  {y \<in> set xs.
    (\<forall>k' < k. \<phi> (k', find_last y xs))}"

context with_threshold
begin

(* Given fixed xs and phi,
    the state having processed i elements *)
definition eager_state_inv :: "'a list \<Rightarrow> coin_matrix \<Rightarrow> 'a state \<Rightarrow> bool"
  where "eager_state_inv xs \<phi> state \<equiv>
  (state_chi state =
    nondet_alg_aux (state_k state) xs \<phi>)"

lemma eager_step_1_inv:
  assumes i:"i < length xs"
  assumes inv: "eager_state_inv (take i xs) \<phi> state"
  shows "
    eager_state_inv (take (i+1) xs) \<phi>
      (run_reader (eager_step_1 xs i state) \<phi>)"
  using assms
  unfolding eager_step_1_def eager_state_inv_def nondet_alg_aux_def
  apply (auto simp add: run_reader_simps Let_def  find_last_before_def)
  sorry

lemma eager_step_2_inv:
  assumes i:"i < length xs"
  assumes inv: "eager_state_inv (take (i+1) xs) \<phi> state"
  shows "
    eager_state_inv (take (i+1) xs) \<phi>
      (run_reader (eager_step_2 xs i state) \<phi>)"
  using inv
  unfolding eager_step_2_def eager_state_inv_def nondet_alg_aux_def
  apply (auto simp add: run_reader_simps Let_def  find_last_before_def)
  by (metis add.commute find_last_before_def less_SucE plus_1_eq_Suc)

lemma eager_step_inv:
  assumes i:"i < length xs"
  assumes inv: "eager_state_inv (take i xs) \<phi> state"
  shows "
    eager_state_inv (take (i+1) xs) \<phi>
      (run_reader (eager_step xs i state) \<phi>)"
  by (metis eager_step_1_inv eager_step_2_inv eager_step_split i inv run_reader_simps(3))

lemma eager_algorithm_inv:
  shows "eager_state_inv xs \<phi>
      (run_reader (eager_algorithm xs) \<phi>)"
proof (induction xs rule:rev_induct)
  case Nil
  then show ?case
    by (auto simp add: eager_algorithm_def run_reader_simps eager_state_inv_def initial_state_def nondet_alg_aux_def)
next
  case (snoc x xs)
  then show ?case
    apply (auto simp add: eager_algorithm_snoc)
    by (metis (no_types, lifting) append_eq_conv_conj eager_step_inv length_append_singleton lessI list.sel(1) run_reader_simps(3) semiring_norm(174) take_hd_drop)
qed

lemma rel_pmf_eager_algorithm_nondet_alg_aux:
  "rel_pmf (\<lambda>st Y. state_k st = K \<longrightarrow> state_chi st = Y)
    (map_pmf (run_reader (eager_algorithm xs)) (prod_pmf ({..<n}\<times>{..<n}) (\<lambda>_. coin_pmf)))
    (map_pmf (nondet_alg_aux K xs) (prod_pmf ({..<n}\<times>{..<n}) (\<lambda>_. coin_pmf)))"
  unfolding pmf.rel_map
  apply (intro rel_pmf_reflI)
  by (meson eager_algorithm_inv eager_state_inv_def)

(* We may want to further rephrase the RHS *)
lemma eager_algorithm_nondet_measureD:
  shows "
  measure_pmf.prob
    (map_pmf (run_reader (eager_algorithm xs)) (prod_pmf ({..<n}\<times>{..<n}) (\<lambda>_. coin_pmf)))
    {st. state_k st = K \<and> P (state_chi st)} \<le>
  measure_pmf.prob
    (map_pmf (nondet_alg_aux K xs) (prod_pmf ({..<n}\<times>{..<n}) (\<lambda>_. coin_pmf)))
    {Y. P Y}" (is "measure_pmf.prob ?p ?A \<le> measure_pmf.prob ?q ?B")
proof -
  from rel_pmf_measureD[OF rel_pmf_eager_algorithm_nondet_alg_aux]
  have "measure_pmf.prob ?p ?A \<le>
    measure_pmf.prob ?q
      {y. \<exists>x\<in>?A. state_k x = K \<longrightarrow> state_chi x = y}" .
  also have "... = measure_pmf.prob ?q {Y. P Y}"
    apply (intro arg_cong[where f = "measure_pmf.prob ?q"])
    apply clarsimp
    by (metis simps(1) simps(2))
  finally show ?thesis .
qed

lemma uncurry_prod_coin_pmf:
  shows "(prod_pmf ({..<n::nat}\<times>{..<n}) (\<lambda>_. coin_pmf)) =
    map_pmf (\<lambda>\<omega>. \<lambda>x\<in>{..<n} \<times> {..<n}.
              \<omega> (snd x) (fst x))
      (prod_pmf {..<n} (\<lambda>_. prod_pmf {..<n} (\<lambda>_. coin_pmf)))"
  apply (subst prod_pmf_swap)
  subgoal by auto
  apply (subst prod_pmf_uncurry)
  by (auto intro!: map_pmf_cong simp add: map_pmf_comp o_def fun_eq_iff)

lemma map_pmf_nondet_alg_aux_eq:
  assumes "length xs \<le> n" "K \<le> n"
  shows "
    map_pmf (nondet_alg_aux K xs)
      (prod_pmf ({..<n}\<times>{..<n}) (\<lambda>_. coin_pmf)) =
    map_pmf (\<lambda>f. {y \<in> set xs. \<forall>k'<K. f y k'})
     (prod_pmf (set xs)
       (\<lambda>_. prod_pmf {..<n} (\<lambda>_. coin_pmf)))"
proof -
  have 1: "(\<lambda>f. nondet_alg_aux K xs
            (\<lambda>xa\<in>{..<n} \<times> {..<n}. f (snd xa) (fst xa))) =
     (\<lambda>f. {y \<in> set xs. (\<forall>k' < K. f y k')})
        \<circ>
     (\<lambda>f. \<lambda>i\<in>set xs. f (find_last i xs))"
    using assms
    by (auto simp add: fun_eq_iff nondet_alg_aux_def dual_order.strict_trans1 find_last_correct_1(2))

  have "map_pmf (nondet_alg_aux K xs)
     (prod_pmf ({..<n} \<times> {..<n})
       (\<lambda>_. coin_pmf)) =
    map_pmf
     (\<lambda>f. nondet_alg_aux K xs
            (\<lambda>xa\<in>{..<n} \<times> {..<n}.  f (snd xa) (fst xa)))
     (prod_pmf {..<n}
       (\<lambda>_. prod_pmf {..<n}
              (\<lambda>_. coin_pmf)))"
    unfolding uncurry_prod_coin_pmf map_pmf_comp by auto
  also have "... =
    map_pmf (\<lambda>f. {y \<in> set xs. \<forall>k'<K. f y k'})
     (prod_pmf (set xs)
       (\<lambda>_. prod_pmf {..<n} (\<lambda>_. coin_pmf)))"
    unfolding 1 map_pmf_compose
    apply (clarsimp simp add: o_def)
    apply (subst prod_pmf_reindex)
    apply (auto simp add: o_def find_last_inj)
    using assms(1) find_last_correct_1(2) by fastforce
  finally show ?thesis .
qed
  
end

end
