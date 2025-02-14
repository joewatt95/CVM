theory CVM_Algo_Nondet_Binomial

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Utils_Approx_Algo
  CVM_Algo_Lazy_Eager

begin

definition nondet_algo ::
  \<open>'a list \<Rightarrow> nat \<Rightarrow> coin_matrix \<Rightarrow> 'a set\<close> where
  \<open>nondet_algo \<equiv> \<lambda> xs k \<phi>.
    {x \<in> set xs. \<forall> k' < k. curry \<phi> k' (last_index xs x)}\<close>

definition state_inv ::
  \<open>'a list \<Rightarrow> coin_matrix \<Rightarrow> 'a state \<Rightarrow> bool\<close> where
  \<open>state_inv \<equiv> \<lambda> xs \<phi> state.
    state_chi state = nondet_algo xs (state_k state) \<phi>\<close>

lemmas state_inv_def' =
  state_inv_def[simplified nondet_algo_def set_eq_iff, simplified]

context cvm_algo_assms
begin

theorem
  fixes xs
  defines \<open>state_inv_take \<equiv> state_inv <<< flip take xs\<close>
  shows
    initial_state_inv :
      \<open>state_inv [] \<phi> initial_state\<close> (is \<open>PROP ?thesis_0\<close>) and

    step_1_eager_inv : \<open>\<And> idx.
      idx < length xs \<Longrightarrow> \<turnstile>rd
        \<lbrakk>state_inv_take idx\<rbrakk>
        step_1_eager xs idx
        \<lbrakk>state_inv_take (Suc idx)\<rbrakk>\<close> (is \<open>PROP ?thesis_1\<close>) and

    step_2_eager_inv : \<open>\<And> idx. \<turnstile>rd
      \<lbrakk>state_inv_take (Suc idx)\<rbrakk>
      step_2_eager xs idx
      \<lbrakk>state_inv_take (Suc idx)\<rbrakk>\<close> (is \<open>PROP ?thesis_2\<close>) and

    step_eager_inv : \<open>\<And> idx.
      idx < length xs \<Longrightarrow> \<turnstile>rd
        \<lbrakk>state_inv_take idx\<rbrakk>
        (step_eager xs idx)
        \<lbrakk>state_inv_take (Suc idx)\<rbrakk>\<close> (is \<open>PROP ?thesis_3\<close>) and

    run_steps_eager_inv : \<open>\<turnstile>rd
      \<lbrakk>state_inv []\<rbrakk> run_steps_eager xs \<lbrakk>state_inv xs\<rbrakk>\<close> (is \<open>PROP ?thesis_4\<close>)
proof -
  show \<open>PROP ?thesis_0\<close> by (simp add: state_inv_def' initial_state_def)

  show \<open>PROP ?thesis_1\<close>
    unfolding step_1_eager_def' state_inv_def' state_inv_take_def
    by (simp add: take_Suc_conv_app_nth)

  moreover show \<open>PROP ?thesis_2\<close>
    unfolding step_2_eager_def' state_inv_def' last_index_up_to_def state_inv_take_def
    apply simp
    by (smt (z3) last_index_less length_take less_Suc_eq less_Suc_eq_le min.absorb2 min.cobounded2)
  
  ultimately show \<open>PROP ?thesis_3\<close>
    unfolding step_eager_def by (simp add: in_set_enumerate_eq)
 
  with loop[where offset = 0 and P = state_inv_take and xs = \<open>[0 ..< length xs]\<close>]
  show \<open>PROP ?thesis_4\<close>
    unfolding state_inv_take_def by (simp add: in_set_enumerate_eq)
qed

context
  fixes m n :: nat
begin

private abbreviation (input)
  \<open>prob_bernoulli_matrix \<equiv> \<lambda> P. \<P>(\<phi> in bernoulli_matrix m n f. P \<phi>)\<close>

context
  fixes k and xs 
  assumes assms : \<open>k \<le> m\<close> \<open>length xs \<le> n\<close> 
begin

lemma map_pmf_nondet_algo_eq :
  \<open>map_pmf (nondet_algo xs k)
    (bernoulli_matrix m n f) =
  map_pmf (\<lambda> P. {x \<in> set xs. P x})
    (prod_pmf (set xs) \<lblot>bernoulli_pmf <| f ^ k\<rblot>)\<close>
  (is \<open>?L = ?R\<close>)
proof -
  let ?m' = \<open>{..< m}\<close> let ?n' = \<open>{..< n}\<close>
  let ?M = \<open>\<lambda> I. prod_pmf I \<lblot>prod_pmf {..< m} \<lblot>coin_pmf\<rblot>\<rblot>\<close>

  have \<open>?L =
    map_pmf
      (\<lambda> \<phi>. nondet_algo xs k (\<lambda> (x, y) \<in> ?m' \<times> ?n'. \<phi> y x))
      (?M ?n')\<close>
    unfolding bernoulli_matrix_eq_uncurry_prod
    apply (subst prod_pmf_swap_uncurried)
    by (simp_all add: map_pmf_comp)

  also have \<open>\<dots> = (
    ?M ?n'
      |> map_pmf (\<lambda> P. \<lambda> x \<in> set xs. P (last_index xs x))
      |> map_pmf (\<lambda> P. {x \<in> set xs. \<forall> k' < k. P x k'}))\<close>
    unfolding nondet_algo_def map_pmf_comp
    using assms by (auto intro: map_pmf_cong)

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
    apply (intro map_pmf_cong Pi_pmf_cong refl)
    apply (cases k)
    by simp_all

  finally show ?thesis .
qed

theorem map_pmf_nondet_algo_eq_binomial :
  \<open>map_pmf (card <<< nondet_algo xs k) (bernoulli_matrix m n f) =
    binomial_pmf (card <| set xs) (f ^ k)\<close>
  (is \<open>map_pmf (?card_nondet_algo _ _) _ = _\<close>)
proof -
  let ?go = \<open>\<lambda> g. map_pmf (g xs k) (bernoulli_matrix m n f)\<close>

  have \<open>?go ?card_nondet_algo = map_pmf card (?go nondet_algo)\<close>
    by (simp add: map_pmf_comp)

  with assms show ?thesis
    apply (subst binomial_pmf_altdef')
    by (simp_all add: map_pmf_nondet_algo_eq power_le_one map_pmf_comp)
qed

corollary prob_eager_algo_le_binomial :
  \<open>prob_bernoulli_matrix (\<lambda> \<phi>.
    let state = run_reader (run_steps_eager xs initial_state) \<phi>
    in state_k state = k \<and> P (card <| state_chi state))
  \<le> \<P>(estimate in binomial_pmf (card <| set xs) <| f ^ k. P estimate)\<close>
  (is \<open>prob_bernoulli_matrix ?P_run_steps_eager \<le> ?prob_P_binomial\<close>)
proof -
  from initial_state_inv run_steps_eager_inv
  have \<open>?P_run_steps_eager \<phi> \<Longrightarrow> P (card <| nondet_algo xs k \<phi>)\<close>
    (is \<open>_ \<Longrightarrow> ?P_nondet_algo \<phi>\<close>) for \<phi> by (metis state_inv_def)

  then have
    \<open>prob_bernoulli_matrix ?P_run_steps_eager
    \<le> prob_bernoulli_matrix ?P_nondet_algo\<close>
    by (auto intro: pmf_mono)

  also have \<open>\<dots> = ?prob_P_binomial\<close>
    by (simp flip: map_pmf_nondet_algo_eq_binomial)

  finally show ?thesis .
qed

end

abbreviation
  \<open>run_steps_eager_then_step_1 \<equiv> \<lambda> i xs.
    run_steps_eager (take i xs) initial_state \<bind> step_1_eager xs i\<close>

corollary prob_eager_algo_then_step_1_le_binomial :
  assumes \<open>k \<le> m\<close> \<open>i < length xs\<close> \<open>length xs \<le> n\<close>
  shows
    \<open>prob_bernoulli_matrix (\<lambda> \<phi>.
      let state = run_reader (run_steps_eager_then_step_1 i xs) \<phi>
      in state_k state = k \<and> P (card <| state_chi state))
    \<le> \<P>(estimate in binomial_pmf (card <| set <| take (Suc i) xs) <| f ^ k.
        P estimate)\<close>
  (is \<open>prob_bernoulli_matrix ?P_run_steps_eager_then_step_1 \<le> ?prob_P_binomial\<close>)
proof -
  from \<open>i < length xs\<close> initial_state_inv run_steps_eager_inv step_1_eager_inv
  have
    \<open>?P_run_steps_eager_then_step_1 \<phi> \<Longrightarrow>
    P (card <| nondet_algo (take (Suc i) xs) k \<phi>)\<close>
    (is \<open>_ \<Longrightarrow> ?P_nondet_algo \<phi>\<close>) for \<phi>
    by (metis run_reader_simps(3)[of "foldM (\<bind>) return_rd (step_eager (take i xs)) [0..<length (take i xs)] initial_state" "step_1_eager xs i" \<phi>] state_inv_def)

  then have
    \<open>prob_bernoulli_matrix ?P_run_steps_eager_then_step_1
    \<le> prob_bernoulli_matrix ?P_nondet_algo\<close>
    by (auto intro: pmf_mono)

  also from assms
  have \<open>\<dots> = ?prob_P_binomial\<close> by (simp flip: map_pmf_nondet_algo_eq_binomial)

  finally show ?thesis .
qed

end

end

end