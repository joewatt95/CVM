theory Distinct_Elems_Nondet

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  CVM.Utils_Approx_Algo
  CVM.Distinct_Elems_Eager

begin

(* After processing the list xs, the chi is the set of
     distinct elements x in xs where the last time
     we flipped coins for x, the first k elements were heads. *)
definition nondet_alg_aux ::
  "nat \<Rightarrow> 'a list \<Rightarrow> coin_matrix \<Rightarrow> 'a set" where
  "nondet_alg_aux k xs \<phi> =
    {x \<in> set xs. \<forall> k' < k. curry \<phi> k' (find_last x xs)}"

definition nondet_alg :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> (nat \<times> nat \<Rightarrow> bool) \<Rightarrow> nat\<close> where
  \<open>nondet_alg k xs = nondet_alg_aux k xs >>> card\<close>

context with_threshold
begin

(* Given fixed xs and phi,
    the state having processed i elements *)
definition eager_state_inv ::
  "'a list \<Rightarrow> coin_matrix \<Rightarrow> 'a state \<Rightarrow> bool" where
  "eager_state_inv xs \<phi> state \<equiv>
    (state_chi state = nondet_alg_aux (state_k state) xs \<phi>)"

lemma eager_step_1_inv :
  assumes
    \<open>i < length xs\<close>
    \<open>eager_state_inv (take i xs) \<phi> state\<close>
  shows
    \<open>eager_state_inv
      (take (i + 1) xs)
      \<phi>
      (run_reader (eager_step_1 xs i state)  \<phi>)\<close>
  using
    assms
    find_last_before_self_eq[OF \<open>i < length xs\<close>]
    find_last_before_eq_find_last_iff[OF \<open>i < length xs\<close>]
  by (fastforce simp add:
    eager_step_1_def eager_state_inv_def nondet_alg_aux_def run_reader_simps
    find_last_before_def take_Suc_conv_app_nth)

lemma eager_step_2_inv:
  assumes
    "i < length xs"
    "eager_state_inv (take (i+1) xs) \<phi> state"
  shows "
    eager_state_inv (take (i+1) xs) \<phi>
      (run_reader (eager_step_2 xs i state) \<phi>)"
  using assms
  by (auto
    elim: less_SucE
    simp add:
      eager_step_2_def eager_state_inv_def nondet_alg_aux_def run_reader_simps
      find_last_before_def Let_def)

lemma eager_step_inv:
  assumes
    "i < length xs"
    "eager_state_inv (take i xs) \<phi> state"
  shows "
    eager_state_inv (take (i + 1) xs) \<phi>
      (run_reader (eager_step xs i state) \<phi>)"
  by (metis assms eager_step_1_inv eager_step_2_inv eager_step_def run_reader_simps(3))

lemma eager_algorithm_inv:
  shows "eager_state_inv xs \<phi>
      (run_eager_algorithm xs \<phi>)"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case
    by (auto simp add: eager_algorithm_def run_steps_def run_reader_simps eager_state_inv_def initial_state_def nondet_alg_aux_def)
next
  case (snoc _ _)
  then show ?case
    apply (simp add: eager_algorithm_snoc)
    by (metis (no_types, lifting) append_eq_conv_conj eager_step_inv length_append_singleton lessI list.sel(1) run_reader_simps(3) semiring_norm(174) take_hd_drop)
qed

(* lemma rel_pmf_eager_algorithm_nondet_alg_aux:
  \<open>rel_pmf
    (\<lambda> state X. state_k state = K \<longrightarrow> state_chi state = X)
    (map_pmf (run_eager_algorithm xs) p)
    (map_pmf (nondet_alg_aux K xs) p)\<close>
  using eager_algorithm_inv
  by (fastforce
    intro: rel_pmf_reflI
    simp add: bernoulli_matrix_def pmf.rel_map eager_state_inv_def) *)

context
  fixes f xs
  assumes
    eager_state_inv_f : \<open>\<And> \<phi>. eager_state_inv xs \<phi> (run_reader (f xs) \<phi>)\<close>
begin

lemma rel_pmf_nondet_alg_aux :
  \<open>rel_pmf
    (\<lambda> state X. state_k state = K \<longrightarrow> state_chi state = X)
    (map_pmf (run_reader <| f xs) p)
    (map_pmf (nondet_alg_aux K xs) p)\<close>
  using eager_state_inv_f
  by (fastforce
    intro: rel_pmf_reflI
    simp add: bernoulli_matrix_def pmf.rel_map eager_state_inv_def)

(* We may want to further rephrase the RHS *)
lemma nondet_measureD :
  \<open>measure_pmf.prob
    (map_pmf (run_reader <| f xs) p)
    {state. state_k state = K \<and> P (state_chi state)}
  \<le> measure_pmf.prob
      (map_pmf (nondet_alg_aux K xs) p)
      {Y. P Y}\<close>
  (is "measure_pmf.prob ?p ?A \<le> measure_pmf.prob ?q ?B")
proof -
  have
    \<open>measure_pmf.prob ?p ?A
      \<le> measure_pmf.prob ?q
        {y. \<exists> x \<in> ?A. state_k x = K \<longrightarrow> state_chi x = y}\<close>
    using rel_pmf_measureD rel_pmf_nondet_alg_aux by blast

  also have \<open>... = measure_pmf.prob ?q {Y. P Y}\<close>
    by (metis (mono_tags, lifting) mem_Collect_eq simps(1) simps(2))

  finally show ?thesis .
qed

(* lemma eager_algorithm_nondet_measureD:
  \<open>measure_pmf.prob
    (map_pmf (run_eager_algorithm xs) p)
    {state. state_k state = K \<and> P (state_chi state)}
  \<le> measure_pmf.prob
      (map_pmf (nondet_alg_aux K xs) p)
      {Y. P Y}\<close>
  (is "measure_pmf.prob ?p ?A \<le> measure_pmf.prob ?q ?B")
proof -
  have
    \<open>measure_pmf.prob ?p ?A
      \<le> measure_pmf.prob ?q
        {y. \<exists> x \<in> ?A. state_k x = K \<longrightarrow> state_chi x = y}\<close>
    sorry

  also have \<open>... = measure_pmf.prob ?q {Y. P Y}\<close>
    by (metis (mono_tags, lifting) mem_Collect_eq simps(1) simps(2))

  finally show ?thesis .
qed *)

end

end

end