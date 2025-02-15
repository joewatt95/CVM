theory CVM_Algo_Lazy_Eager

imports
  "List-Index.List_Index"
  CVM_Algo_No_Fail
  Utils_Reader_Monad
  Utils_PMF_Lazify

begin

hide_const (open) Misc_CryptHOL.coin_pmf

type_synonym coin_matrix = \<open>nat \<times> nat \<Rightarrow> bool\<close>

context cvm_algo_assms
begin

context
  fixes xs :: \<open>'a list\<close> and i :: nat
begin

definition step_1_lazy :: \<open>'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_1_lazy \<equiv> \<lambda> state. do {
    let k = state_k state; let chi = state_chi state;
    insert_x_into_chi \<leftarrow> bernoulli_pmf <| f ^ k;
    let chi = (chi |>
      if insert_x_into_chi
      then insert (xs ! i)
      else Set.remove (xs ! i));
    return_pmf (state\<lparr>state_chi := chi\<rparr>) }\<close>

definition step_2_lazy :: \<open>'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_2_lazy \<equiv> \<lambda> state. do {
    let k = state_k state; let chi = state_chi state;
    if card chi = threshold
    then do {
      keep_in_chi \<leftarrow> prod_pmf chi \<lblot>bernoulli_pmf f\<rblot>;
      return_pmf \<lparr>state_k = k + 1, state_chi = Set.filter keep_in_chi chi\<rparr> }
    else return_pmf state }\<close>

definition step_lazy :: \<open>'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_lazy \<equiv> \<lambda> state. step_1_lazy state \<bind> step_2_lazy\<close>

lemmas step_1_lazy_def' = step_1_lazy_def[
  simplified map_pmf_def[symmetric] Let_def if_distribR]

lemmas step_2_lazy_def' = step_2_lazy_def[
  simplified map_pmf_def[symmetric] map_comp_rd Let_def]

end

abbreviation
  \<open>run_steps_lazy \<equiv> \<lambda> xs. foldM_pmf (step_lazy xs) [0 ..< length xs]\<close>

lemma step_lazy_cong :
  assumes "xs ! i = ys ! i"
  shows "step_lazy xs i = step_lazy ys i"
  unfolding step_lazy_def step_1_lazy_def' step_2_lazy_def'
  using assms by (simp cong: if_cong)

lemma run_steps_lazy_snoc :
  \<open>run_steps_lazy (xs @ [x]) state =
    run_steps_lazy xs state \<bind> step_lazy (xs @ [x]) (length xs)\<close>
  by (fastforce
    intro: bind_pmf_cong foldM_cong step_lazy_cong
    simp add: foldM_pmf_snoc upt_Suc_append nth_append_left)

abbreviation \<open>well_formed_state \<equiv> \<lambda> xs state.
  state_k state \<le> length xs \<and> state_chi state \<subseteq> set xs\<close>

lemma run_steps_lazy_preserves_well_formedness :
  \<open>AE state in run_steps_lazy xs initial_state. well_formed_state xs state\<close>
  (is \<open>AE state in _. ?P (length xs) state\<close>)
proof -
  have \<open>\<turnstile>pmf
    \<lbrakk>(\<lambda> state.
      (index, i) \<in> set (List.enumerate 0 [0 ..< length xs]) \<and>
      ?P index state)\<rbrakk>
    step_lazy xs i
    \<lbrakk>?P (Suc index)\<rbrakk>\<close> for index i
    unfolding step_lazy_def step_1_lazy_def' step_2_lazy_def'
    by (auto simp add: AE_measure_pmf_iff in_set_enumerate_eq)

  then show ?thesis
    apply (intro Utils_PMF_FoldM_Hoare.loop[
      where offset = 0 and xs = \<open>[0 ..< length xs]\<close>, simplified])
    by (auto simp add: initial_state_def)
qed

theorem run_steps_no_fail_eq_lazy :
  \<open>run_steps_no_fail xs initial_state = run_steps_lazy xs initial_state\<close>
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)

  moreover have
    \<open>step_lazy (xs @ [x]) (length xs) state = step_no_fail x state\<close> for state
    unfolding
      step_lazy_def step_1_lazy_def' step_2_lazy_def' step_1_def' step_2_def'
      bind_map_pmf
    apply (intro bind_pmf_cong refl)
    by simp

  ultimately show ?case
    unfolding run_steps_lazy_snoc foldM_pmf_snoc by presburger
qed

context
  fixes xs :: \<open>'a list\<close> and i :: nat
begin

definition step_1_eager ::
  \<open>'a state \<Rightarrow> (coin_matrix, 'a state) reader_monad\<close> where
  \<open>step_1_eager \<equiv> \<lambda> state. do {
    let k = state_k state; let chi = state_chi state;
    \<phi> \<leftarrow> get_rd;
    let chi = (chi |>
      if \<forall> k' < k. \<phi> (k', i)
      then insert (xs ! i)
      else Set.remove (xs ! i));
    return_rd (state\<lparr>state_chi := chi\<rparr>) }\<close>

definition last_index_up_to :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> nat\<close> where
  \<open>last_index_up_to \<equiv> \<lambda> k xs. min k <<< last_index (take (Suc k) xs)\<close>

definition step_2_eager ::
  \<open>'a state \<Rightarrow> (coin_matrix, 'a state) reader_monad\<close> where
  \<open>step_2_eager \<equiv> \<lambda> state. do {
    let k = state_k state; let chi = state_chi state;
    if real (card chi) = threshold
    then do {
      \<phi> \<leftarrow> get_rd;
      let chi = Set.filter
        (\<lambda> x \<in> chi. \<phi> (k, last_index_up_to i xs x)) chi;
      return_rd \<lparr>state_k = Suc k, state_chi = chi\<rparr> }
    else return_rd state }\<close>

definition step_eager ::
  \<open>'a state \<Rightarrow> (nat \<times> nat \<Rightarrow> bool, 'a state) reader_monad\<close> where
  \<open>step_eager \<equiv> \<lambda> state. step_1_eager state \<bind> step_2_eager\<close>

lemmas step_1_eager_def' = step_1_eager_def[
  simplified map_rd_def[symmetric] Let_def if_distribR]

lemmas step_2_eager_def' = step_2_eager_def[
  simplified map_rd_def[symmetric] Let_def]

end

abbreviation
  \<open>run_steps_eager \<equiv> \<lambda> xs. foldM_rd (step_eager xs) [0 ..< length xs]\<close>

lemma step_eager_cong :
  assumes \<open>i < length xs\<close> \<open>i < length ys\<close> \<open>take (Suc i) xs = take (Suc i) ys\<close>
  shows
    \<open>step_1_eager xs i = step_1_eager ys i\<close> (is ?thesis_0)
    \<open>step_2_eager xs i = step_2_eager ys i\<close> (is ?thesis_1)
    \<open>step_eager xs i = step_eager ys i\<close> (is ?thesis_2)
proof -
  from assms have \<open>xs ! i = ys ! i\<close> by (simp add: take_Suc_conv_app_nth)

  moreover from assms have
    \<open>last_index_up_to i xs = last_index_up_to i ys\<close>
    unfolding last_index_up_to_def by simp
 
  ultimately show ?thesis_0 ?thesis_1 ?thesis_2
    unfolding step_eager_def step_1_eager_def' step_2_eager_def'
    by (simp_all cong: if_cong)
qed

lemma run_steps_eager_snoc :
  \<open>run_steps_eager (xs @ [x]) state =
    run_steps_eager xs state \<bind> step_eager (xs @ [x]) (length xs)\<close>
  by (fastforce
    intro: bind_cong_rd foldM_cong step_eager_cong
    simp add: foldM_rd_snoc upt_Suc_append nth_append_left)

abbreviation \<open>coin_pmf \<equiv> bernoulli_pmf f\<close>

context
  fixes n :: nat
begin

interpretation lazify "{..< n} \<times> {..< n}" "undefined" "\<lambda> _. coin_pmf"
  by unfold_locales simp

lemma depends_on_step_1 :
  fixes xs x \<phi> state
  shows "depends_on
    (step_1_eager (xs @ [x]) l state)
    ({..< state_k state} \<times> {l})"
    (is \<open>depends_on _ ?S\<close>)
proof -
  have "c1 (k',l) = c2 (k',l)"
    if "restrict c1 ?S = restrict c2 ?S" "k' < state_k state"
    for c1 c2 :: "nat \<times> nat \<Rightarrow> bool" and k'
  proof -
    have "c1 (k',l) = restrict c1 ?S (k',l)" using that(2) by simp
    also have "\<dots> = restrict c2 ?S (k',l)" using that(1) by simp
    also have "\<dots> = c2 (k',l)" using that(2) by simp
    finally show ?thesis by simp
  qed

  thus ?thesis
    unfolding step_1_eager_def' Let_def
    apply (intro depends_on_map_get)
    by auto
qed

lemma depends_on_step_2 :
  fixes \<sigma>
  defines
    "k' \<equiv> state_k \<sigma> + of_bool (card (state_chi \<sigma>) = threshold)"
  shows "depends_on
    (step_2_eager (xs @ [x]) l \<sigma>)
    ({state_k \<sigma> ..< k'} \<times> {.. l})"
proof (cases "card (state_chi \<sigma>) = threshold")
  case False
  then show ?thesis unfolding step_2_eager_def' by (simp add:Let_def depends_on_return)
next
  define keep_in_chi :: "(coin_matrix, 'a \<Rightarrow> bool) reader_monad" where
    "keep_in_chi \<equiv> map_rd
      (\<lambda> \<phi>. \<lambda> i \<in> state_chi \<sigma>. \<phi> (state_k \<sigma>, last_index_up_to l (xs @ [x]) i))
      get_rd"

  case True
  then have b: "k' = Suc (state_k \<sigma>)" unfolding k'_def by simp

  from True depends_on_return
  have a:"step_2_eager (xs @ [x]) l \<sigma> =
    map_rd
      (\<lambda>c. \<lparr>state_k = (Suc <| state_k \<sigma>), state_chi = Set.filter c (state_chi \<sigma>)\<rparr>)
      keep_in_chi"
    unfolding step_2_eager_def' keep_in_chi_def by (simp add: map_comp_rd)

  have "depends_on keep_in_chi ({state_k \<sigma>} \<times> {.. l})"
    unfolding keep_in_chi_def last_index_up_to_def
    apply (intro depends_on_map_get ext)
    apply simp
    by (metis SigmaI atMost_iff insertI1 min.cobounded1 restrict_apply')

  then show ?thesis unfolding a b by (auto intro: depends_on_map)
qed

lemma depends_on_step_2_eq :
  "depends_on
    (map_rd ((=) v) (step_2_eager (xs @ [x]) l \<sigma>))
    ({state_k \<sigma> ..< state_k v} \<times> {.. l})"
proof (cases "state_k v = state_k \<sigma> + of_bool (card (state_chi \<sigma>) = threshold)")
  case True
  then show ?thesis by (simp add: depends_on_map depends_on_step_2)
next
  case False
  then have "map_rd ((=) v) (step_2_eager (xs @ [x]) l \<sigma>) = return_rd False"
    unfolding step_2_eager_def
    by (intro reader_monad_eqI) (auto simp add: Let_def)
  then show ?thesis by (simp add:depends_on_return)
qed

lemma independent_bind_step :
  "independent_bind
    (step_1_eager (xs @ [x]) (length xs) \<sigma>)
    (step_2_eager (xs @ [x]) (length xs))"
proof (intro independent_bindI[where F = "\<lambda> v. {..< state_k v} \<times> UNIV"] conjI)
  fix v
  show "depends_on
    (map_rd ((=) v) (step_1_eager (xs @ [x]) (length xs) \<sigma>))
    ({..< state_k v} \<times> UNIV)"
  proof (cases "state_k v = state_k \<sigma>")
    case True
    then show ?thesis
      by (auto intro: depends_on_map depends_on_mono[OF depends_on_step_1])
  next
    case False
    then have
      "map_rd ((=) v) (step_1_eager (xs @ [x]) (length xs) \<sigma>) = return_rd False"
      unfolding step_1_eager_def' by (auto intro: reader_monad_eqI simp add: Let_def)
    then show ?thesis using depends_on_return by simp
  qed

  show "depends_on (step_2_eager (xs @ [x]) (length xs) v) (UNIV - {..< state_k v} \<times> UNIV)"
    by (intro depends_on_mono[OF depends_on_step_2]) auto
qed

lemma eager_lazy_step:
  fixes xs
  defines "l \<equiv> length xs"
  assumes "length (xs @ [x]) \<le> n" "state_k \<sigma> < n" "state_chi \<sigma> \<subseteq> set xs"
  shows "sample (step_eager (xs@[x]) l \<sigma>) = step_lazy (xs@[x]) l \<sigma>"
    (is "?L = ?R")
proof -
  have l_lt_n: "l < n" unfolding l_def using assms(2) by simp

  have "measure space {x. \<forall>k'<state_k \<sigma>. x (k', l)} = measure space (({..<state_k \<sigma>}\<times>{l}) \<rightarrow> {True})"
    by (auto intro: measure_pmf_cong)
  also have "\<dots> = (\<Prod>j \<in> {..<state_k \<sigma>}\<times>{l}. measure coin_pmf {True})"
    using assms(3) l_lt_n unfolding space_def by (fastforce intro: prob_prod_pmf')
  also have "\<dots> = f ^ state_k \<sigma>" by (simp add:measure_pmf_single)

  finally have
    "bernoulli_pmf (f ^ state_k \<sigma>) = map_pmf (\<lambda>\<phi>. \<forall>k'<state_k \<sigma>. \<phi> (k', l)) space"
    by (simp add: bool_pmf_eq_iff_pmf_True_eq pmf_map vimage_def power_le_one)

  also have "\<dots> = sample (map_rd (\<lambda>\<phi>. \<forall>k'<state_k \<sigma>. \<phi> (k', l)) get_rd)"
    unfolding sample_def by (auto intro: map_pmf_cong)

  finally have step_1 :
    "sample (step_1_eager (xs@[x]) l \<sigma>) = step_1_lazy (xs@[x]) l \<sigma>"
    unfolding step_1_eager_def' step_1_lazy_def'
    by (simp add: lazify_map map_pmf_comp)

  have step_2 :
    "sample (step_2_eager (xs@[x]) l \<sigma>') = step_2_lazy \<sigma>'" (is "?L1 = ?R1")
    if "state_chi \<sigma>' \<subseteq> insert x (state_chi \<sigma>)" "state_k \<sigma>' = state_k \<sigma>" for \<sigma>'
  proof (cases "real (card (state_chi \<sigma>')) = threshold")
    case False
    then show ?thesis unfolding step_2_eager_def' step_2_lazy_def' by (simp add:lazify_return)
  next
    case True
    let ?f = "\<lambda> i. (state_k \<sigma>', last_index_up_to l (xs @ [x]) i)"

    from that(2) assms(3) have b: "?f ` state_chi \<sigma>' \<subseteq> {..< n} \<times> {..< n}"
      unfolding last_index_up_to_def
      apply (intro image_subsetI)
      using dual_order.strict_trans2 infinite_cartesian_product l_lt_n by auto

    have "inj_on (last_index (xs @ [x])) (set (xs @ [x]))"
      using inj_on_last_index by blast
    hence "inj_on (last_index_up_to l (xs @ [x])) (set (xs @ [x]))"
      unfolding last_index_up_to_def l_def
      by (smt (verit, del_insts) inf.absorb4 inf_min inj_on_cong last_index_less_size_conv length_append_singleton less_Suc_eq less_or_eq_imp_le min_def take_all_iff)
    moreover have "inj (\<lambda> i. (state_k \<sigma>', i))" by (intro inj_onI) auto
    ultimately have "inj_on ((\<lambda> i. (state_k \<sigma>', i)) \<circ> (last_index_up_to l (xs@[x]))) (set (xs@[x]))"
      using inj_on_subset by (intro comp_inj_on) fastforce+
    hence "inj_on ?f (set (xs@[x]))" unfolding comp_def by simp
    moreover have "state_chi \<sigma>' \<subseteq> set (xs@[x])" using assms(4) that by auto
    ultimately have c:"inj_on ?f (state_chi \<sigma>')" using inj_on_subset by blast

    have
      "prod_pmf (state_chi \<sigma>') (\<lblot>coin_pmf\<rblot> <<< ?f) =
        sample (map_rd (\<lambda>\<phi>. \<lambda>i\<in>state_chi \<sigma>'. \<phi> (?f i)) get_rd)"
      (is "?L' = ?R'")
    proof - 
      have "?R' = map_pmf (\<lambda>\<phi>. \<lambda>i\<in>state_chi \<sigma>'. \<phi> (?f i)) space"
        unfolding sample_def by (auto intro: map_pmf_cong)
      also have "\<dots> = ?L'"
        unfolding space_def by (intro prod_pmf_reindex b c) auto
      finally show ?thesis by simp
    qed

    with True show ?thesis
      unfolding step_2_eager_def' step_2_lazy_def'
      by (simp add: lazify_map map_pmf_comp)
  qed

  have "?L = sample (step_1_eager (xs@[x]) l \<sigma>) \<bind> (\<lambda>\<sigma>'. sample (step_2_eager (xs@[x]) l \<sigma>'))"
    unfolding step_eager_def l_def by (intro lazify_bind independent_bind_step)
  also have "\<dots> = step_1_lazy (xs@[x]) l \<sigma> \<bind> (\<lambda>\<sigma>'. sample (step_2_eager (xs@[x]) l \<sigma>'))"
    unfolding step_1 by simp
  also have "\<dots>  = step_1_lazy (xs@[x]) l \<sigma> \<bind> step_2_lazy"
    by (intro bind_pmf_cong refl step_2)
      (auto simp add:step_1_lazy_def nth_append l_def cong:if_cong split:if_split_asm)
  also have "\<dots> = ?R" unfolding step_lazy_def by simp
  finally show ?thesis by simp
qed

lemma depends_on_step_approx :
  "depends_on
    (step_eager (xs @ [x]) l \<sigma>)
    ({state_k \<sigma> ..< Suc (state_k \<sigma>)} \<times> {.. l} \<union> {..< state_k \<sigma>} \<times> {l})"
proof -
  have "state_k \<sigma>' = state_k \<sigma>"
    if "\<sigma>' \<in> set_pmf (sample (step_1_eager (xs @ [x]) l \<sigma>))" for \<sigma>'
    using that by (auto simp add:step_1_eager_def sample_def)

  thus ?thesis unfolding step_eager_def
    by (intro depends_on_bind depends_on_mono[OF depends_on_step_1]
        depends_on_mono[OF depends_on_step_2]) auto
qed

lemma depends_on_step :
  "depends_on
    (map_rd ((=) v) (step_eager (xs @ [x]) l \<sigma>))
    ({state_k \<sigma> ..< state_k v} \<times> {.. l} \<union> {..< state_k \<sigma>} \<times> {l})"
  (is "depends_on _ ?S")
proof -
  show ?thesis unfolding step_eager_def
  proof (intro depends_on_bind_eq conjI)
    fix w assume "w \<in> set_pmf (sample (step_1_eager (xs @ [x]) l \<sigma>))"

    then have "state_k \<sigma> = state_k w"
      unfolding sample_def step_1_eager_def by auto 

    then show "depends_on (map_rd ((=) v) (step_2_eager (xs @ [x]) l w)) ?S"
      by (auto intro: depends_on_mono[OF depends_on_step_2_eq])

    show "depends_on (map_rd ((=) w) (step_1_eager (xs @ [x]) l \<sigma>)) ?S"
      by (auto intro: depends_on_map depends_on_mono[OF depends_on_step_1])
  qed
qed

lemma depends_on_algorithm :
  "depends_on
    (map_rd ((=) v) (run_steps_eager xs initial_state))
    ({..< state_k v} \<times> {..< length xs})"
    (is \<open>depends_on _ (?S v xs)\<close>)
proof (induction xs arbitrary:v rule:rev_induct)
  case Nil
  then show ?case by (simp add: depends_on_return map_rd_def depends_on_bind)
next
  case (snoc x xs)
  show ?case unfolding run_steps_eager_snoc
  proof (intro depends_on_bind_eq conjI)
    fix w
    assume
      "w \<in> set_pmf (sample (run_steps_eager xs initial_state))"
      "v \<in> set_pmf (sample (step_eager (xs @ [x]) (length xs) w))"

    hence a: "state_k w \<le> state_k v"
      unfolding sample_def by (auto simp: step_eager_def step_1_eager_def' step_2_eager_def')

    from a show "depends_on
      (map_rd ((=) w) (run_steps_eager xs initial_state))
      (?S v <| xs @ [x])"
      by (auto intro: depends_on_mono[OF snoc])

    from a show "depends_on
      (map_rd ((=) v) (step_eager (xs @ [x]) (length xs) w))
      (?S v <| xs @ [x])"
      by (auto intro: depends_on_mono[OF depends_on_step])
  qed
qed

lemma independent_bind :
  fixes xs :: "'a list"
  defines "F \<equiv> \<lambda> v :: 'a state. {..< state_k v} \<times> {..< length xs}"
  shows "independent_bind
    (run_steps_eager xs initial_state)
    (step_eager (xs @ [x]) (length xs))"
proof (intro independent_bindI[where F = F] conjI)
  fix v

  show "depends_on
    (map_rd ((=) v) (run_steps_eager xs initial_state)) (F v)"
    unfolding F_def by (intro depends_on_algorithm)

  show "depends_on
    (step_eager (xs @ [x]) (length xs) v)
    (UNIV - F v)"
    unfolding F_def
    by (auto intro: depends_on_mono[OF depends_on_step_approx]) 
qed

text \<open>Equivalence of the algorithm sampling coin flips in advance and the algorithm
sampling lazily.\<close>

theorem sample_run_steps_eager_eq_run_steps_lazy :
  assumes "length xs \<le> n"
  shows
    "sample (run_steps_eager xs initial_state) = run_steps_lazy xs initial_state"
    (is \<open>?L xs = ?R xs\<close>)
using assms proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by (simp add: lazify_return)
next
  case (snoc x xs)
  then have
    a: "[0..<length (xs @ [x])] = [0..<length xs]@[length xs]" and
    b: "length xs \<le> n" by simp_all 

  have "?L (xs @ [x]) = sample (run_steps_eager xs initial_state \<bind> step_eager (xs @ [x]) (length xs))"
    unfolding run_steps_eager_snoc by simp
  also have "\<dots> = run_steps_lazy xs initial_state \<bind> (\<lambda> r. sample (step_eager (xs@[x]) (length xs) r))"
    unfolding snoc(1)[OF b, symmetric] by (intro lazify_bind independent_bind)
  also have "\<dots> = run_steps_lazy xs initial_state \<bind> step_lazy (xs@[x]) (length xs)"
    using run_steps_lazy_preserves_well_formedness snoc(2)
    by (fastforce intro: bind_pmf_cong eager_lazy_step simp add: AE_measure_pmf_iff)
  also have "\<dots> = ?R (xs @ [x])" unfolding run_steps_lazy_snoc by simp
  finally show ?case .
qed

corollary run_steps_no_fail_eq_run_steps_eager_bernoulli_matrix :
  assumes "length xs \<le> n"
  shows
    "run_steps_no_fail xs initial_state = (
      bernoulli_matrix n n f
        |> map_pmf (run_reader <| run_steps_eager xs initial_state))"
  using assms run_steps_no_fail_eq_lazy sample_run_steps_eager_eq_run_steps_lazy
  by (metis bernoulli_matrix_def local.space_def sample_def)

end

end

end