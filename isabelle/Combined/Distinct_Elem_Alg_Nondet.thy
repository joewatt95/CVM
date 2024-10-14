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

lemma eager_step_1_inv:
  assumes i:"i < length xs"
  assumes inv: "eager_state_inv (take i xs) \<phi> state"
  shows "
    eager_state_inv (take (i+1) xs) \<phi>
      (run_reader (eager_step_1 xs i state) \<phi>)"
  unfolding eager_step_1_def
  apply (auto simp add: run_reader_simps)
  sorry

lemma eager_step_2_inv:
  assumes i:"i < length xs"
  assumes inv: "eager_state_inv (take (i+1) xs) \<phi> state"
  shows "
    eager_state_inv (take (i+1) xs) \<phi>
      (run_reader (eager_step_2 xs i state) \<phi>)"
  unfolding eager_step_2_def
  apply (auto simp add: run_reader_simps Let_def)
  sorry

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

lemma filter_with_upto:
  shows"
  filter P [0..<n] =
  filter (\<lambda>i. P i \<and> i < n) [0..<n]"
  by (intro filter_cong) auto

lemma find_last_eq:
  assumes "x \<in> set xs"
  shows "map_of (rev (zip xs [0..<length xs])) x = Some (find_last x xs)"
  using assms
proof (induction xs rule:rev_induct)
  case Nil
  then show ?case
    by (auto simp add: find_last_def)
next
  case ih:(snoc x xs)
  have *:"(filter
             (\<lambda>i. (i < length xs \<longrightarrow>
                    xs ! i = xs ! xb) \<and>
                   (\<not> i < length xs \<longrightarrow>
                    [x] ! (i - length xs) = xs ! xb))
             [0..<length xs])
    = filter (\<lambda>i. xs ! i = xs ! xb)
             [0..<length xs]" for xb
    apply (intro filter_cong)
    by auto
  show ?case
    using ih
    apply (auto simp add: nth_append
       find_last_def Let_def filter_empty_conv *
       split: if_splits)
    using atLeastLessThan_iff by blast
qed

lemma nondet_alg_aux_eq_map_of:
  shows "
  nondet_alg_aux k xs \<phi> = (
  let m = map_of (rev (zip xs [0..<length xs])) in
  {y \<in> set xs.
    (\<forall>k' < k. \<phi> (k', the (m y)))})"
  using find_last_eq nondet_alg_aux_def by force

definition nondet_alg :: "nat \<Rightarrow> ((nat \<times> 'a) \<Rightarrow> bool) \<Rightarrow> 'a set"
  where "nondet_alg k \<phi> =
  {y. (\<forall>k' < k. \<phi> (k', y))}"

(* Removing the use of "find_last"? *)
lemma nondet_alg_eq:
  shows "
    map_pmf (nondet_alg_aux K xs) (prod_pmf ({..<n}\<times>{..<n}) (\<lambda>_. coin_pmf)) =
    map_pmf (nondet_alg K) (prod_pmf ({..<n}\<times> set xs) (\<lambda>_. coin_pmf))"
  sorry

end

end