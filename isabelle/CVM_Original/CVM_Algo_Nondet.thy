theory CVM_Algo_Nondet

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Utils_Approx_Algo
  CVM_Algo_Lazy_Eager

begin

(* After processing the list xs, the chi is the set of
     distinct elements x in xs where the last time
     we flipped coins for x, the first k elements were heads. *)
definition nondet_alg_aux ::
  "nat \<Rightarrow> 'a list \<Rightarrow> coin_matrix \<Rightarrow> 'a set" where
  "nondet_alg_aux \<equiv> \<lambda> k xs \<phi>.
    {x \<in> set xs. \<forall> k' < k. curry \<phi> k' (last_index xs x)}"

definition state_inv ::
  "'a list \<Rightarrow> coin_matrix \<Rightarrow> 'a state \<Rightarrow> bool" where
  "state_inv \<equiv> \<lambda> xs \<phi> state.
    state_chi state = nondet_alg_aux (state_k state) xs \<phi>"

context cvm_algo_assms
begin

lemma step_1_eager_inv :
  assumes
    \<open>i < length xs\<close>
    \<open>state_inv (take i xs) \<phi> state\<close>
  shows
    \<open>state_inv (take (Suc i) xs) \<phi> (run_reader (step_1_eager xs i state) \<phi>)\<close>
  using assms
  unfolding step_1_eager_def' state_inv_def nondet_alg_aux_def
  by (auto simp add: run_reader_simps take_Suc_conv_app_nth)

lemma step_2_eager_inv:
  assumes
    "i < length xs"
    "state_inv (take (Suc i) xs) \<phi> state"
  shows "state_inv (take (Suc i) xs) \<phi> (run_reader (step_2_eager xs i state) \<phi>)"
  using assms
  unfolding step_2_eager_def' state_inv_def nondet_alg_aux_def last_index_up_to_def
  (* TODO: Speed up proof. *)
  by (auto
    elim!: less_SucE
    simp add: run_reader_simps take_Suc_conv_app_nth)

lemma step_eager_inv :
  assumes
    "i < length xs"
    "state_inv (take i xs) \<phi> state"
  shows "state_inv (take (Suc i) xs) \<phi> (run_reader (step_eager xs i state) \<phi>)"
  by (metis assms step_1_eager_inv step_2_eager_inv step_eager_def run_reader_simps(3))

lemma eager_algorithm_inv:
  "state_inv xs \<phi> <| run_reader (run_steps_eager xs initial_state) \<phi>"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case
    by (auto simp add: run_reader_simps state_inv_def initial_state_def nondet_alg_aux_def)
next
  case (snoc _ _)
  with step_eager_inv show ?case
    apply simp
    by (smt (verit, ccfv_SIG) append_eq_conv_conj cvm_algo_assms.step_eager_inv cvm_algo_assms_axioms length_append_singleton lessI list.sel(1) list.size(3,3) run_reader_simps(3)
      run_steps_eager_snoc take.simps(1) take_all_iff take_hd_drop upt_Suc_append)
qed

lemma nondet_measureD :
  assumes \<open>\<And> \<phi>. state_inv xs \<phi> (run_reader m \<phi>)\<close>
  shows
    \<open>\<P>(state in map_pmf (run_reader m) p.
      state_k state = k \<and> P (state_chi state))
    \<le> \<P>(chi in map_pmf (nondet_alg_aux k xs) p. P chi)\<close>
  apply simp 
  by (metis (mono_tags, lifting) assms state_inv_def mem_Collect_eq pmf_mono)

end

end