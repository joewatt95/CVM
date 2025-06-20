theory Distinct_Elems_Algo_Transforms_Eager

imports
  Utils_List
  Utils_PMF_Lazify
  Utils_PMF_Bernoulli_Binomial
  Utils_Reader_Monad_Hoare
  Distinct_Elems_Algo_Transforms_Lazy

begin

hide_const (open) Misc_CryptHOL.coin_pmf

type_synonym coin_matrix = \<open>nat \<times> nat \<Rightarrow> bool\<close>

definition step_1_eager :: "'a list \<Rightarrow> nat \<Rightarrow> 'a state \<Rightarrow> (coin_matrix, 'a state) reader_monad"
  where "step_1_eager xs i state = do {
      let k = state_k state;
      let chi = state_chi state;
      insert_x_into_chi \<leftarrow> map_rd (\<lambda>\<phi>. (\<forall>k'<k. \<phi> (k', i))) get_rd;

      let chi = (chi |>
        if insert_x_into_chi
        then insert (xs ! i)
        else Set.remove (xs ! i));
      return_rd (state \<lparr>state_chi := chi\<rparr>)
    }"

context with_threshold
begin

definition step_2_eager :: "'a list \<Rightarrow> nat \<Rightarrow> 'a state \<Rightarrow> (coin_matrix, 'a state) reader_monad"
  where "step_2_eager xs i state = do {
      let k = state_k state;
      let chi = state_chi state;
      if real (card chi) < threshold then
        return_rd (state\<lparr>state_chi := chi\<rparr>)
      else do {
        keep_in_chi \<leftarrow> map_rd (\<lambda>\<phi>. \<lambda>x \<in> chi. \<phi> (k, find_last_before i x xs)) get_rd;
        let chi = Set.filter keep_in_chi chi;
        return_rd \<lparr>state_k = k+1, state_chi = chi\<rparr>
      }
    }"

definition eager_step :: "'a list \<Rightarrow> nat \<Rightarrow> 'a state \<Rightarrow> (coin_matrix, 'a state) reader_monad"
  where
  "eager_step xs i state = step_1_eager xs i state \<bind> step_2_eager xs i"

definition eager_algorithm ::
  "'a list \<Rightarrow> (nat \<times> nat \<Rightarrow> bool, 'a state) reader_monad" where
  "eager_algorithm \<equiv> run_steps_from_state foldM_rd eager_step initial_state"

abbreviation \<open>run_eager_algorithm \<equiv> run_reader <<< eager_algorithm\<close>

lemma eager_step_cong:
  assumes "i < length xs" "i < length ys"
  assumes "take (i+1) xs = take (i+1) ys"
  shows
    "step_1_eager xs i = step_1_eager ys i"
    "step_2_eager xs i = step_2_eager ys i"
    "eager_step xs i = eager_step ys i"
proof -
  have "xs ! i = ys ! i" by (metis less_add_one nth_take assms(3))
  moreover have "find_last_before i x xs = find_last_before i x ys" for x
    unfolding find_last_before_def assms(3) by simp
  ultimately show
    "step_1_eager xs i = step_1_eager ys i"
    "step_2_eager xs i = step_2_eager ys i"
    "eager_step xs i = eager_step ys i"
    unfolding eager_step_def step_1_eager_def step_2_eager_def
    by (auto simp add: Let_def cong: if_cong)
qed

lemma eager_algorithm_snoc:
  "eager_algorithm (xs@[x]) = eager_algorithm xs \<bind> eager_step (xs@[x]) (length xs)"
proof -
  have a: "[0..<length (xs @ [x])] = [0..<length xs]@[length xs]" by simp

  show ?thesis
    unfolding eager_algorithm_def run_steps_from_state_def a foldM_rd_snoc
    by (intro foldM_cong arg_cong2[where f="bind_rd"] eager_step_cong) auto
qed

lemmas eager_algo_simps =
  eager_algorithm_snoc initial_state_def run_steps_from_state_def
  eager_step_def step_1_eager_def step_2_eager_def Let_def run_reader_simps

lemma
  defines [simp] : \<open>state_k_bounded \<equiv> \<lambda> i \<phi> state. state_k state \<le> i\<close>
  shows 
    initial_state_k_bounded :
      \<open>state_k_bounded i \<phi> initial_state\<close> (is ?thesis_0) and
    run_eager_steps_k_bounded : \<open>\<turnstile>rd
      \<lbrakk>state_k_bounded 0\<rbrakk>
      (flip (run_steps_from_state foldM_rd eager_step) xs)
      \<lbrakk>state_k_bounded (length xs)\<rbrakk>\<close>
      (is ?thesis_1) and
    eager_algorithm_k_bounded :
      \<open>state_k (run_eager_algorithm xs \<phi>) \<le> length xs\<close> (is ?thesis_2)
proof -
  show ?thesis_0 by (simp add: initial_state_def)

  moreover show ?thesis_1
  proof -
    have \<open>\<turnstile>rd
      \<lbrakk>(\<lambda> \<phi> state.
      (i, x) \<in> set (List.enumerate 0 [0..<length xs]) \<and>
        state_k_bounded i \<phi> state)\<rbrakk>
      eager_step xs x
      \<lbrakk>state_k_bounded (Suc i)\<rbrakk>\<close> for i x
      unfolding
        run_steps_from_state_def eager_step_def step_1_eager_def Let_def
        step_2_eager_def map_rd_def
      by (auto
        intro!:
          Utils_Reader_Monad_Hoare.seq'[where Q = \<open>state_k_bounded i\<close>]
          Utils_Reader_Monad_Hoare.if_then_else
          Utils_Reader_Monad_Hoare.postcond_true
        intro: Utils_Reader_Monad_Hoare.seq')

    with Utils_Reader_Monad_Hoare.loop[
      where offset = 0 and xs = \<open>[0 ..< length xs]\<close>]
    show ?thesis unfolding run_steps_from_state_def by fastforce
  qed

  ultimately show ?thesis_2
    by (simp add: Utils_Reader_Monad_Hoare.hoare_triple_def eager_algorithm_def initial_state_def)
qed

abbreviation "coin_pmf \<equiv> bernoulli_pmf (1/2)"

context
  fixes n :: nat
begin

interpretation lazify "{..<n} \<times> {..<n}" "undefined" "\<lambda>_. coin_pmf"
  by unfold_locales simp

lemma depends_on_step1:
  fixes xs x \<phi> state
  defines "l \<equiv> length xs"
  shows "depends_on (step_1_eager (xs @ [x]) l state) ({..<state_k state}\<times>{l})"
proof -
  let ?S = "{..<state_k state} \<times> {l}"

  have "c1 (k',l) = c2 (k',l)" if "restrict c1 ?S = restrict c2 ?S" "k' < state_k state"
  for c1 c2 :: "nat \<times> nat \<Rightarrow> bool" and k'
  proof -
    have "c1 (k',l) = restrict c1 ?S (k',l)" using that(2) by simp
    also have "... = restrict c2 ?S (k',l)" using that(1) by simp
    also have "... = c2 (k',l)" using that(2) by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    unfolding step_1_eager_def Let_def
    by (intro depends_on_bind depends_on_return depends_on_map) auto
qed

lemma depends_on_step2:
  fixes xs x \<sigma>
  defines "k' \<equiv> state_k \<sigma> + of_bool (card (state_chi \<sigma>) \<ge> threshold)"
  defines "l \<equiv> length xs"
  shows "depends_on (step_2_eager (xs @ [x]) l \<sigma>) ({state_k \<sigma>..<k'}\<times>{..<l+1})"
proof (cases "card (state_chi \<sigma>) < threshold")
  case True
  then show ?thesis unfolding step_2_eager_def by (simp add:Let_def depends_on_return)
next
  case False
  define keep_in_chi :: "(coin_matrix, 'a \<Rightarrow> bool) reader_monad" where
    "keep_in_chi = map_rd (\<lambda>\<phi>.\<lambda>i \<in> state_chi \<sigma>. \<phi> (state_k \<sigma>, find_last_before l i (xs @ [x]))) get_rd"

  have b: "k' = state_k \<sigma>+1" unfolding k'_def using False by simp

  have a:"step_2_eager (xs @ [x]) l \<sigma> =
    keep_in_chi \<bind> (\<lambda>c. return_rd \<lparr>state_k = (state_k \<sigma>+1), state_chi = Set.filter c (state_chi \<sigma>)\<rparr>)"
    using False unfolding step_2_eager_def by (simp flip: keep_in_chi_def)

  have "c1 (state_k \<sigma>, find_last_before l i (xs @ [x])) = c2 (state_k \<sigma>, find_last_before l i (xs @ [x]))"
    (is "?L = ?R")
    if "restrict c1 ({state_k \<sigma>} \<times> {..<l + 1}) = restrict c2 ({state_k \<sigma>} \<times> {..<l + 1})"
    for c1 c2 :: coin_matrix and i
  proof -
    have "?L = restrict c1 ({state_k \<sigma>} \<times> {..<l + 1}) (state_k \<sigma>, find_last_before l i (xs @ [x]))"
      by (intro restrict_apply'[symmetric]) (simp add: find_last_before_bound le_imp_less_Suc)
    also have "... = restrict c2 ({state_k \<sigma>} \<times> {..<l + 1}) (state_k \<sigma>, find_last_before l i (xs @ [x]))"
      using that by simp
    also have "... = ?R" by (intro restrict_apply') (simp add: find_last_before_bound le_imp_less_Suc)
    finally show ?thesis by simp
  qed

  hence "depends_on keep_in_chi ({state_k \<sigma>} \<times> {..<l + 1})"
    unfolding keep_in_chi_def by (intro depends_on_map ext) auto

  thus ?thesis unfolding a b by (intro depends_on_bind depends_on_return) simp
qed

lemma depends_on_step2_eq:
  fixes xs x \<sigma>
  defines "l \<equiv> length xs"
  shows "depends_on (map_rd ((=) v) (step_2_eager (xs @ [x]) l \<sigma>)) ({state_k \<sigma>..<state_k v}\<times>{..<l+1})"
proof (cases "state_k v = state_k \<sigma> + of_bool (card (state_chi \<sigma>) \<ge> threshold)")
  case True
  show ?thesis unfolding map_rd_def l_def True
    by (intro depends_on_bind depends_on_step2 depends_on_return)
next
  case False
  hence "map_rd ((=) v) (step_2_eager (xs @ [x]) l \<sigma>) = return_rd False"
    unfolding step_2_eager_def
    by (intro reader_monad_eqI) (auto simp add:run_reader_simps Let_def)
  then show ?thesis by (simp add:depends_on_return)
qed

lemma independent_bind_step:
  "independent_bind (step_1_eager (xs@[x]) (length xs) \<sigma>) (step_2_eager (xs@[x]) (length xs))"
proof (intro independent_bindI[where F="\<lambda>v. {..<state_k v}\<times>UNIV"] conjI)
  fix v
  show "depends_on (map_rd ((=) v) (step_1_eager (xs @ [x]) (length xs) \<sigma>)) ({..<state_k v} \<times> UNIV)"
  proof (cases "state_k v = state_k \<sigma>")
    case True
    thus ?thesis
      unfolding map_rd_def by (intro depends_on_bind depends_on_return depends_on_mono[OF depends_on_step1]) auto
  next
    case False
    hence "map_rd ((=) v) (step_1_eager (xs @ [x]) (length xs) \<sigma>) = return_rd False"
      unfolding step_1_eager_def by (intro reader_monad_eqI) (auto simp add:run_reader_simps Let_def)
    then show ?thesis
      using depends_on_return by simp
  qed

  show "depends_on (step_2_eager (xs @ [x]) (length xs) v) (UNIV - {..<state_k v} \<times> UNIV)"
    by (intro depends_on_mono[OF depends_on_step2]) auto
qed

lemma eager_lazy_step:
  fixes xs
  defines "l \<equiv> length xs"
  assumes "length (xs@[x]) \<le> n" "state_k \<sigma> < n" "state_chi \<sigma> \<subseteq> set xs"
  shows "sample (eager_step (xs@[x]) l \<sigma>) = lazy_step (xs@[x]) l \<sigma>"
    (is "?L = ?R")
proof -
  have l_le_n: "l < n" unfolding l_def using assms(2) by simp

  have "measure space {x. \<forall>k'<state_k \<sigma>. x (k', l)} = measure space (({..<state_k \<sigma>}\<times>{l}) \<rightarrow> {True})"
    by (intro measure_pmf_cong) auto
  also have "... = (\<Prod>j \<in> {..<state_k \<sigma>}\<times>{l}. measure coin_pmf {True})"
    using assms(3) l_le_n unfolding space_def by (intro prob_prod_pmf' subsetI) auto
  also have "... = (1/2) ^ state_k \<sigma>" by (simp add:measure_pmf_single)
  also have "... = 1 / 2 ^ state_k \<sigma>" unfolding power_one_over by simp
  finally have "1 / 2 ^ state_k \<sigma> = measure space {x. \<forall>k'<state_k \<sigma>. x (k', l)}" by simp
  hence "bernoulli_pmf (1/2^state_k \<sigma>) = map_pmf (\<lambda>\<phi>. \<forall>k'<state_k \<sigma>. \<phi> (k', l)) space"
    by (intro bool_pmf_eqI) (simp add:pmf_map vimage_def)
  also have "... = sample (map_rd (\<lambda>\<phi>. \<forall>k'<state_k \<sigma>. \<phi> (k', l)) get_rd)"
    unfolding sample_def by (intro map_pmf_cong refl) (simp add:run_reader_simps)
  finally have a: "sample (map_rd (\<lambda>\<phi>. \<forall>k'<state_k \<sigma>. \<phi> (k', l)) get_rd) = bernoulli_pmf (1/2^state_k \<sigma>)"
    by simp

  have step_1: "sample (step_1_eager (xs@[x]) l \<sigma>) = step_1_lazy (xs@[x]) l \<sigma>"
    unfolding step_1_eager_def Let_def step_1_lazy_def by (subst lazify_bind_return) (simp_all add:a)

  have step_2: "sample (step_2_eager (xs@[x]) l \<sigma>') = step_2_lazy (xs@[x]) l \<sigma>'" (is "?L1 = ?R1")
    if "state_chi \<sigma>' \<subseteq> insert x (state_chi \<sigma>)" "state_k \<sigma>' = state_k \<sigma>" for \<sigma>'
  proof (cases "real (card (state_chi \<sigma>')) < threshold")
    case True
    then show ?thesis unfolding step_2_eager_def step_2_lazy_def by (simp add:lazify_return)
  next
    case False
    let ?f = "\<lambda>i. (state_k \<sigma>', find_last_before l i (xs @ [x]))"

    have b: "?f ` state_chi \<sigma>' \<subseteq> {..<n} \<times> {..<n}" using that(2) assms(3)
      by (intro image_subsetI)
        (auto intro!:dual_order.strict_trans2[OF l_le_n] find_last_before_bound)

    have "inj_on (\<lambda>i. find_last i (xs @ [x])) (set (xs @ [x]))" by (intro find_last_inj)
    hence "inj_on (\<lambda>i. find_last_before l i (xs @ [x])) (set (xs @ [x]))"
      unfolding find_last_before_def l_def by (simp add:find_last_inj)
    moreover have "inj (\<lambda>i. (state_k \<sigma>',i))" by (intro inj_onI) auto
    ultimately have "inj_on ((\<lambda>i. (state_k \<sigma>',i)) \<circ> (\<lambda>i. find_last_before l i (xs@[x]))) (set (xs@[x]))"
      using inj_on_subset by (intro comp_inj_on) force+
    hence "inj_on ?f (set (xs@[x]))" unfolding comp_def by simp
    moreover have "state_chi \<sigma>' \<subseteq> set (xs@[x])" using assms(4) that by auto
    ultimately have c:"inj_on ?f (state_chi \<sigma>')" using inj_on_subset by blast

    have "sample (map_rd (\<lambda>\<phi>. \<lambda>i\<in>state_chi \<sigma>'. \<phi> (?f i)) get_rd) = map_pmf (\<lambda>\<phi>. \<lambda>i\<in>state_chi \<sigma>'. \<phi> (?f i)) space"
      unfolding sample_def by (intro map_pmf_cong refl) (simp add:run_reader_simps)
    also have "... = prod_pmf (state_chi \<sigma>') ((\<lambda>_. coin_pmf) \<circ> ?f)"
      unfolding space_def by (intro prod_pmf_reindex b c) auto
    also have "... = prod_pmf (state_chi \<sigma>') (\<lambda>_. coin_pmf)" by (simp add:comp_def)
    finally have "sample (map_rd (\<lambda>\<phi>. \<lambda>i\<in>state_chi \<sigma>'. \<phi> (?f i)) get_rd) = prod_pmf (state_chi \<sigma>') (\<lambda>_. coin_pmf)"
      by simp
    thus ?thesis unfolding step_2_eager_def Let_def  using False
      by (simp add:step_2_eager_def Let_def lazify_bind_return step_2_lazy_def)
  qed

  have "?L = sample (step_1_eager (xs@[x]) l \<sigma>) \<bind> (\<lambda>\<sigma>'. sample (step_2_eager (xs@[x]) l \<sigma>'))"
    unfolding eager_step_def l_def by (intro lazify_bind independent_bind_step)
  also have "... = step_1_lazy (xs@[x]) l \<sigma> \<bind> (\<lambda>\<sigma>'. sample (step_2_eager (xs@[x]) l \<sigma>'))"
    unfolding step_1 by simp
  also have "... = step_1_lazy (xs@[x]) l \<sigma> \<bind> step_2_lazy (xs@[x]) l"
    by (intro bind_pmf_cong refl step_2)
      (auto simp add:step_1_lazy_def nth_append l_def cong:if_cong split:if_split_asm)
  also have "... = ?R" unfolding lazy_step_def by simp
  finally show ?thesis by simp
qed

lemma depends_on_step_approx:
  fixes xs
  defines "l \<equiv> length xs"
  shows "depends_on (eager_step (xs @ [x]) l \<sigma>) ({state_k \<sigma>..<state_k \<sigma>+1}\<times>{..<l+1} \<union> {..<state_k \<sigma>}\<times>{l})"
proof -
  have "state_k \<sigma>' = state_k \<sigma>" if "\<sigma>' \<in> set_pmf (sample (step_1_eager (xs @ [x]) l \<sigma>))" for \<sigma>'
    using that unfolding l_def by (simp add:step_1_eager_def sample_def)
      (auto simp add:run_reader_simps)

  thus ?thesis unfolding eager_step_def l_def
    by (intro depends_on_bind depends_on_mono[OF depends_on_step1]
        depends_on_mono[OF depends_on_step2]) auto
qed

lemma depends_on_step:
  fixes xs
  defines "l \<equiv> length xs"
  shows "depends_on (map_rd ((=) v) (eager_step (xs @ [x]) l \<sigma>)) ({state_k \<sigma>..<state_k v}\<times>{..<l+1} \<union> {..<state_k \<sigma>}\<times>{l})"
proof -
  show ?thesis unfolding l_def eager_step_def
  proof (intro depends_on_bind_eq conjI)
    fix w
    assume a:"w \<in> set_pmf (sample (step_1_eager (xs @ [x]) (length xs) \<sigma>))"
    assume "v \<in> set_pmf (sample (step_2_eager (xs @ [x]) (length xs) w))"

    show "depends_on (map_rd ((=) w) (step_1_eager (xs @ [x]) (length xs) \<sigma>))
          ({state_k \<sigma>..<state_k v} \<times> {..<length xs + 1} \<union> {..<state_k \<sigma>} \<times> {length xs})"
      unfolding map_rd_def
      by (intro depends_on_bind depends_on_mono[OF depends_on_step1] depends_on_return) auto

    have "state_k \<sigma> = state_k w"
      using a unfolding sample_def step_1_eager_def by (auto simp:run_reader_simps)
    thus "depends_on (map_rd ((=) v) (step_2_eager (xs @ [x]) (length xs) w))
          ({state_k \<sigma>..<state_k v} \<times> {..<length xs + 1} \<union> {..<state_k \<sigma>} \<times> {length xs})"
      by (intro depends_on_mono[OF depends_on_step2_eq]) auto
  qed
qed

lemma depends_on_algorithm:
   "depends_on (map_rd ((=) v) (eager_algorithm xs)) ({..<state_k v} \<times> {..<length xs})"
proof (induction xs arbitrary:v rule:rev_induct)
  case Nil
  then show ?case by (simp add: eager_algorithm_def run_steps_from_state_def depends_on_return map_rd_def depends_on_bind)
next
  case (snoc x xs)
  show ?case
    unfolding eager_algorithm_snoc
  proof (intro depends_on_bind_eq conjI)
    fix w
    assume "w \<in> set_pmf (sample (eager_algorithm xs))"
    assume "v \<in> set_pmf (sample (eager_step (xs @ [x]) (length xs) w))"

    hence a: "state_k w \<le> state_k v"
      unfolding sample_def by (auto simp:Let_def run_reader_simps eager_step_def step_1_eager_def step_2_eager_def)

    show "depends_on (map_rd ((=) w) (eager_algorithm xs)) ({..<state_k v} \<times> {..<length (xs @ [x])})"
      using a by (intro depends_on_mono[OF snoc]) auto

    show "depends_on (map_rd ((=) v) (eager_step (xs @ [x]) (length xs) w)) ({..<state_k v} \<times> {..<length (xs @ [x])})"
      using a by (intro depends_on_mono[OF depends_on_step]) auto
  qed
qed

lemma independent_bind:
  "independent_bind (eager_algorithm xs) (eager_step (xs @ [x]) (length xs))"
proof (intro independent_bindI[where F="\<lambda>v. {..<state_k v} \<times> {..<length xs}"] conjI)
  fix v

  show "depends_on (map_rd ((=) v) (eager_algorithm xs)) ({..<state_k v} \<times> {..<length xs})"
    by (intro depends_on_algorithm)

  show "depends_on (eager_step (xs @ [x]) (length xs) v) (UNIV - {..<state_k v} \<times> {..<length xs})"
    by (intro depends_on_mono[OF depends_on_step_approx]) (auto)
qed

text \<open>Equivalence of the algorithm sampling coin flips in advance and the algorithm
sampling lazily.\<close>

lemma eager_lazy_conversion_aux:
  "length xs \<le> n \<Longrightarrow> sample (eager_algorithm xs) = lazy_algorithm xs"
proof (induction xs rule:rev_induct)
  case Nil
  then show ?case by (simp add: eager_algorithm_def lazy_algorithm_def run_steps_from_state_def lazify_return)
next
  case (snoc x xs)

  have a: "[0..<length (xs @ [x])] = [0..<length xs]@[length xs]" by simp
  have b: "length xs \<le> n" using snoc by simp

  have "sample (eager_algorithm (xs@[x])) = sample (eager_algorithm xs \<bind> eager_step (xs @ [x]) (length xs))"
    unfolding eager_algorithm_snoc by simp
  also have "... = lazy_algorithm xs \<bind> (\<lambda>r. sample (eager_step (xs@[x]) (length xs) r))"
    unfolding snoc(1)[OF b, symmetric] by (intro lazify_bind independent_bind)
  also have "... = lazy_algorithm xs \<bind> lazy_step (xs@[x]) (length xs)"
    using state_k_bound state_chi_bound snoc(2) by (intro bind_pmf_cong refl eager_lazy_step snoc(2)) fastforce
  also have "... = lazy_algorithm (xs@[x])"
    unfolding lazy_algorithm_snoc by simp
  finally show ?case by simp
qed

text \<open>Version of the above with the definitions from the locale unfolded. This theorem can be used
outside of this context.\<close>

theorem eager_lazy_conversion:
  assumes "length xs \<le> n"
  shows
    "lazy_algorithm xs = (
      fair_bernoulli_matrix n n
        |> map_pmf (run_eager_algorithm xs))"
  using eager_lazy_conversion_aux[OF assms(1)]
  unfolding bernoulli_matrix_def sample_def space_def by auto

end

end

end