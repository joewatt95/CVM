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
    by (auto simp add: eager_algorithm_def run_steps_from_state_def run_reader_simps eager_state_inv_def initial_state_def nondet_alg_aux_def)
next
  case (snoc _ _)
  then show ?case
    apply (simp add: eager_algorithm_snoc)
    by (metis (no_types, lifting) append_eq_conv_conj eager_step_inv length_append_singleton lessI list.sel(1) run_reader_simps(3) semiring_norm(174) take_hd_drop)
qed

(* We may want to further rephrase the RHS *)
lemma nondet_measureD :
  assumes \<open>\<And> \<phi>. eager_state_inv xs \<phi> (run_reader (f xs) \<phi>)\<close>
  shows
    \<open>\<P>(state in map_pmf (run_reader <| f xs) p.
      state_k state = k \<and> P (state_chi state))
    \<le> \<P>(chi in map_pmf (nondet_alg_aux k xs) p. P chi)\<close>
  apply simp 
  by (metis (mono_tags, lifting) assms eager_state_inv_def mem_Collect_eq pmf_mono)

end

end