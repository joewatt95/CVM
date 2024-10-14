theory Distinct_Elem_Alg_Nondet
  imports
    CVM.Reader_Monad
    CVM.Lazify
    CVM.Utils_List
    Distinct_Elem_Alg_Eager
    "Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF"
    "Monad_Normalisation.Monad_Normalisation"
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

lemma eager_step_inv:
  assumes i:"i < length xs"
  assumes inv: "eager_state_inv (take i xs) \<phi> state"
  shows "
    eager_state_inv (take (i+1) xs) \<phi>
      (run_reader (eager_step xs i state) \<phi>)"
  sorry

lemma eager_algorithm_inv:
  shows "eager_state_inv xs \<phi>
      (run_reader (eager_algorithm xs) \<phi>)"
  unfolding eager_algorithm_def
proof (induction xs)
  case Nil
  then show ?case
    unfolding eager_state_inv_def nondet_alg_aux_def initial_state_def
    by (auto simp add: run_reader_simps)
next
  case (Cons x xs)
  then show ?case
    apply auto
    sorry
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

end

end