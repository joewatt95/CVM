theory Distinct_Elems_Eager

imports
  CVM.Utils_Reader_Monad
  CVM.Utils_PMF_Lazify
  CVM.Utils_List
  CVM.Distinct_Elems_No_Fail

begin

sledgehammer_params [
  (* verbose *)
  minimize = true,
  preplay_timeout = 15,
  timeout = 60,
  max_facts = smart,
  provers = "
    cvc4 z3 verit
    e vampire spass
  "
]

type_synonym coin_matrix = \<open>nat \<times> nat \<Rightarrow> bool\<close>

context with_threshold
begin

definition eager_step :: "'a list \<Rightarrow> nat \<Rightarrow> 'a state \<Rightarrow> (coin_matrix, 'a state) reader_monad"
  where "eager_step xs i state = do {
      let k = state_k state;
      let chi = state_chi state;
      insert_x_into_chi \<leftarrow> map_rd (\<lambda>\<phi>. (\<forall>k'<k. \<phi> (k', i))) get_rd;

      let chi = (chi |>
        if insert_x_into_chi
        then insert (xs ! i)
        else Set.remove (xs ! i));

      if real (card chi) < threshold then
        return_rd (state \<lparr>state_chi := chi\<rparr>)
      else do {
        keep_in_chi \<leftarrow> map_rd (\<lambda>\<phi>. \<lambda>x \<in> chi. \<phi> (k, find_last_before i x xs)) get_rd;
        let chi = Set.filter keep_in_chi chi;
        return_rd (\<lparr>state_k = k+1, state_chi = chi\<rparr>)
      }
    }"

definition eager_algorithm :: "'a list \<Rightarrow> (coin_matrix, 'a state) reader_monad" where
  "eager_algorithm xs = foldM_rd (eager_step xs) [0..<length xs] initial_state"

definition lazy_step :: "'a list \<Rightarrow> nat \<Rightarrow> 'a state \<Rightarrow> 'a state pmf"
  where "lazy_step xs i state = do {
    let k = state_k state;
    let chi = state_chi state;
    insert_x_into_chi \<leftarrow> bernoulli_pmf (1/2^k);

    let chi = (chi |>
      if insert_x_into_chi
      then insert (xs ! i)
      else Set.remove (xs ! i));

    if real (card chi) < threshold then
      return_pmf (state \<lparr>state_chi := chi\<rparr>)
    else do {
      keep_in_chi \<leftarrow> Pi_pmf chi undefined (\<lambda>_. bernoulli_pmf (1/2));
      let chi = Set.filter keep_in_chi chi;
      return_pmf (\<lparr>state_k = k+1, state_chi = chi\<rparr>)
    }
  }"

definition lazy_algorithm :: "'a list \<Rightarrow> 'a state pmf" where
  "lazy_algorithm xs = foldM_pmf (lazy_step xs) [0..<length xs] initial_state"

definition eager_step_1 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a state \<Rightarrow> (coin_matrix, 'a state) reader_monad"
  where "eager_step_1 xs i state = do {
      let k = state_k state;
      let chi = state_chi state;
      insert_x_into_chi \<leftarrow> map_rd (\<lambda>\<phi>. (\<forall>k'<k. \<phi> (k', i))) get_rd;

      let chi = (chi |>
        if insert_x_into_chi
        then insert (xs ! i)
        else Set.remove (xs ! i));
      return_rd (state \<lparr>state_chi := chi\<rparr>)
    }"

definition eager_step_2 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a state \<Rightarrow> (coin_matrix, 'a state) reader_monad"
  where "eager_step_2 xs i state = do {
      let k = state_k state;
      let chi = state_chi state;
      if real (card chi) < threshold then
        return_rd (state \<lparr>state_chi := chi\<rparr>)
      else do {
        keep_in_chi \<leftarrow> map_rd (\<lambda>\<phi>. \<lambda>x \<in> chi. \<phi> (k, find_last_before i x xs)) get_rd;
        let chi = Set.filter keep_in_chi chi;
        return_rd (\<lparr>state_k = k+1, state_chi = chi\<rparr>)
      }
    }"

lemma eager_step_split:
  "eager_step xs i state = eager_step_1 xs i state \<bind> eager_step_2 xs i"
  unfolding eager_step_def eager_step_1_def eager_step_2_def
  by (intro reader_monad_eqI) (simp add:Let_def run_reader_simps)

lemma eager_step_cong:
  assumes "i < length xs" "i < length ys"
  assumes "take (i+1) xs = take (i+1) ys"
  shows "eager_step xs i = eager_step ys i"
proof -
  have "xs ! i = ys ! i" by (metis less_add_one nth_take assms(3))
  moreover have "find_last_before i x xs = find_last_before i x ys" for x
    unfolding find_last_before_def assms(3) by simp
  ultimately show ?thesis
    unfolding eager_step_def by (simp add:Let_def cong:if_cong)
qed

lemma eager_algorithm_snoc:
  "eager_algorithm (xs@[x]) = eager_algorithm xs \<bind> eager_step (xs@[x]) (length xs)"
proof -
  have a: "[0..<length (xs @ [x])] = [0..<length xs]@[length xs]" by simp

  show ?thesis
    unfolding eager_algorithm_def a foldM_rd_snoc
    by (intro foldM_cong  arg_cong2[where f="bind_rd"] eager_step_cong) auto
qed

definition lazy_step_1 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a state \<Rightarrow> 'a state pmf"
  where "lazy_step_1 xs i state = do {
    let k = state_k state;
    let chi = state_chi state;
    insert_x_into_chi \<leftarrow> bernoulli_pmf (1/2^k);

    let chi = (chi |>
      if insert_x_into_chi
      then insert (xs ! i)
      else Set.remove (xs ! i));

    return_pmf (state \<lparr>state_chi := chi\<rparr>)
  }"

definition lazy_step_2 :: "'a list \<Rightarrow> nat \<Rightarrow> 'a state \<Rightarrow> 'a state pmf"
  where "lazy_step_2 xs i state = do {
    let k = state_k state;
    let chi = state_chi state;

    if real (card chi) < threshold then
      return_pmf (state \<lparr>state_chi := chi\<rparr>)
    else do {
      keep_in_chi \<leftarrow> Pi_pmf chi undefined (\<lambda>_. bernoulli_pmf (1/2));
      let chi = Set.filter keep_in_chi chi;
      return_pmf (\<lparr>state_k = k+1, state_chi = chi\<rparr>)
    }
  }"

lemma lazy_step_split:
  "lazy_step xs i state = lazy_step_1 xs i state \<bind> lazy_step_2 xs i"
  unfolding lazy_step_def lazy_step_1_def lazy_step_2_def Let_def bind_assoc_pmf bind_return_pmf
  by (intro bind_pmf_cong) auto

lemma lazy_step_cong:
  assumes "xs ! i = ys ! i"
  shows "lazy_step xs i = lazy_step ys i"
  unfolding lazy_step_def using assms by (simp cong:if_cong)

lemma lazy_algorithm_snoc:
  "lazy_algorithm (xs@[x]) = lazy_algorithm xs \<bind> lazy_step (xs@[x]) (length xs)"
proof -
  have a: "[0..<length (xs @ [x])] = [0..<length xs]@[length xs]" by simp

  show ?thesis
    unfolding lazy_algorithm_def a foldM_pmf_snoc
    by (intro foldM_cong bind_pmf_cong refl lazy_step_cong) (auto simp:nth_append)
qed

lemma state_k_bound:
  assumes "\<omega> \<in> set_pmf (lazy_algorithm xs)"
  shows "state_k \<omega> \<le> length xs"
  using assms
proof (induction xs arbitrary:\<omega> rule:rev_induct)
  case Nil
  then show ?case unfolding lazy_algorithm_def initial_state_def by simp
next
  case (snoc x xs)
  let ?n = "length xs"

  obtain \<omega>1 \<omega>2 where \<omega>:
    "\<omega>1 \<in> set_pmf (lazy_algorithm xs)"
    "\<omega>2 \<in> set_pmf (lazy_step_1 (xs@[x]) ?n \<omega>1)"
    "\<omega> \<in> set_pmf (lazy_step_2 (xs@[x]) ?n \<omega>2)"
    using snoc  unfolding lazy_algorithm_snoc lazy_step_split by auto

  have "state_k \<omega>1 \<le> length xs" using snoc \<omega>(1) by simp
  hence "state_k \<omega>2 \<le> length xs" using \<omega>(2) unfolding lazy_step_1_def by auto
  hence "state_k \<omega> \<le> length xs + 1" using \<omega>(3) unfolding lazy_step_2_def
    by (cases "real (card (state_chi \<omega>2)) < threshold") (auto simp add:Let_def)
  thus ?case by simp
qed

lemma state_chi_bound:
  assumes "\<omega> \<in> set_pmf (lazy_algorithm xs)"
  shows "state_chi \<omega> \<subseteq> set xs"
  using assms
proof (induction xs arbitrary:\<omega> rule:rev_induct)
  case Nil
  then show ?case unfolding lazy_algorithm_def initial_state_def by simp
next
  case (snoc x xs)
  let ?n = "length xs"

  obtain \<omega>1 \<omega>2 where \<omega>:
    "\<omega>1 \<in> set_pmf (lazy_algorithm xs)"
    "\<omega>2 \<in> set_pmf (lazy_step_1 (xs@[x]) ?n \<omega>1)"
    "\<omega> \<in> set_pmf (lazy_step_2 (xs@[x]) ?n \<omega>2)"
    using snoc  unfolding lazy_algorithm_snoc lazy_step_split by auto

  have "state_chi \<omega>1 \<subseteq> set xs" using snoc \<omega>(1) by simp
  moreover have "state_chi \<omega>2 \<subseteq> insert x (state_chi \<omega>1)" using \<omega>(2) unfolding lazy_step_1_def
    by (auto simp add:nth_append cong:if_cong split:if_split_asm)
  ultimately have "state_chi \<omega>2 \<subseteq> set (xs@[x])" by auto
  hence "state_chi \<omega> \<subseteq> set (xs@[x])" using \<omega>(3) unfolding lazy_step_2_def
    by (cases "real (card (state_chi \<omega>2)) < threshold") (auto simp:Let_def)
  thus ?case by simp
qed

abbreviation "coin_pmf \<equiv> bernoulli_pmf (1/2)"

lemma depends_on_step1:
  fixes xs x \<phi> state
  defines "n \<equiv> length xs"
  shows "depends_on (eager_step_1 (xs @ [x]) n state) ({..<state_k state}\<times>{n})"
proof -
  let ?S = "{..<state_k state} \<times> {n}"

  have "c1 (k',n) = c2 (k',n)" if "restrict c1 ?S = restrict c2 ?S" "k' < state_k state"
  for c1 c2 :: "nat \<times> nat \<Rightarrow> bool" and k'
  proof -
    have "c1 (k',n) = restrict c1 ?S (k',n)" using that(2) by simp
    also have "... = restrict c2 ?S (k',n)" using that(1) by simp
    also have "... = c2 (k',n)" using that(2) by simp
    finally show ?thesis by simp
  qed
  thus ?thesis
    unfolding eager_step_1_def Let_def
    by (intro depends_on_bind depends_on_return depends_on_map) auto
qed

lemma depends_on_step2:
  fixes xs x \<sigma>
  defines "k' \<equiv> state_k \<sigma> + of_bool (card (state_chi \<sigma>) \<ge> threshold)"
  defines "n \<equiv> length xs"
  shows "depends_on (eager_step_2 (xs @ [x]) n \<sigma>) ({state_k \<sigma>..<k'}\<times>{..<n+1})"
proof (cases "card (state_chi \<sigma>) < threshold")
  case True
  then show ?thesis unfolding eager_step_2_def by (simp add:Let_def depends_on_return)
next
  case False
  define keep_in_chi :: "(coin_matrix, 'a \<Rightarrow> bool) reader_monad" where
    "keep_in_chi = map_rd (\<lambda>\<phi>.\<lambda>i \<in> state_chi \<sigma>. \<phi> (state_k \<sigma>, find_last_before n i (xs @ [x]))) get_rd"

  have b: "k' = state_k \<sigma>+1" unfolding k'_def using False by simp

  have a:"eager_step_2 (xs @ [x]) n \<sigma> =
    keep_in_chi \<bind> (\<lambda>c. return_rd \<lparr>state_k = (state_k \<sigma>+1), state_chi = Set.filter c (state_chi \<sigma>)\<rparr>)"
    using False unfolding eager_step_2_def by (simp add:Let_def keep_in_chi_def[symmetric] depends_on_return)

  have "c1 (state_k \<sigma>, find_last_before n i (xs @ [x])) = c2 (state_k \<sigma>, find_last_before n i (xs @ [x]))"
    (is "?L = ?R")
    if "restrict c1 ({state_k \<sigma>} \<times> {..<n + 1}) = restrict c2 ({state_k \<sigma>} \<times> {..<n + 1})"
    for c1 c2 :: coin_matrix and i
  proof -
    have "?L = restrict c1 ({state_k \<sigma>} \<times> {..<n + 1}) (state_k \<sigma>, find_last_before n i (xs @ [x]))"
      by (intro restrict_apply'[symmetric]) (simp add: find_last_before_bound le_imp_less_Suc)
    also have "... = restrict c2 ({state_k \<sigma>} \<times> {..<n + 1}) (state_k \<sigma>, find_last_before n i (xs @ [x]))"
      using that by simp
    also have "... = ?R" by (intro restrict_apply') (simp add: find_last_before_bound le_imp_less_Suc)
    finally show ?thesis by simp
  qed

  hence "depends_on keep_in_chi ({state_k \<sigma>} \<times> {..<n + 1})"
    unfolding keep_in_chi_def by (intro depends_on_map ext) auto

  thus ?thesis unfolding a b by (intro depends_on_bind depends_on_return) simp
qed

lemma depends_on_step2_eq:
  fixes xs x \<sigma>
  defines "n \<equiv> length xs"
  shows "depends_on (map_rd ((=) v) (eager_step_2 (xs @ [x]) n \<sigma>)) ({state_k \<sigma>..<state_k v}\<times>{..<n+1})"
proof (cases "state_k v = state_k \<sigma> + of_bool (card (state_chi \<sigma>) \<ge> threshold)")
  case True
  show ?thesis unfolding map_rd_def n_def True by (intro depends_on_bind depends_on_step2 depends_on_return)
next
  case False
  hence "map_rd ((=) v) (eager_step_2 (xs @ [x]) n \<sigma>) = return_rd False"
    unfolding eager_step_2_def
    by (intro reader_monad_eqI) (auto simp add:run_reader_simps Let_def)
  then show ?thesis by (simp add:depends_on_return)
qed

lemma independent_bind_step:
  "independent_bind (eager_step_1 (xs@[x]) (length xs) \<sigma>) (eager_step_2 (xs@[x]) (length xs))"
proof (intro independent_bindI[where F="\<lambda>v. {..<state_k v}\<times>UNIV"] conjI)
  fix v
  show "depends_on (map_rd ((=) v) (eager_step_1 (xs @ [x]) (length xs) \<sigma>)) ({..<state_k v} \<times> UNIV)"
  proof (cases "state_k v = state_k \<sigma>")
    case True
    thus ?thesis
      unfolding map_rd_def by (intro depends_on_bind depends_on_return depends_on_mono[OF depends_on_step1]) auto
  next
    case False
    hence "map_rd ((=) v) (eager_step_1 (xs @ [x]) (length xs) \<sigma>) = return_rd False"
      unfolding eager_step_1_def by (intro reader_monad_eqI) (auto simp add:run_reader_simps Let_def)
    then show ?thesis
      using depends_on_return by simp
  qed

  show "depends_on (eager_step_2 (xs @ [x]) (length xs) v) (UNIV - {..<state_k v} \<times> UNIV)"
    by (intro depends_on_mono[OF depends_on_step2]) auto
qed

lemma eager_lazy_step:
  fixes xs
  defines "n \<equiv> length xs"
  assumes "length (xs@[x]) \<le> m" "state_k \<sigma> < m" "state_chi \<sigma> \<subseteq> set xs"
  shows "map_pmf (run_reader (eager_step (xs@[x]) n \<sigma>)) (prod_pmf ({..<m}\<times>{..<m}) (\<lambda>_. coin_pmf)) = lazy_step (xs@[x]) n \<sigma>"
    (is "?L = ?R")
proof -
  let ?pmf = "prod_pmf ({..<m}\<times>{..<m}) (\<lambda>_. coin_pmf)"
  let ?to_pmf = "\<lambda>f. map_pmf (run_reader f) ?pmf"

  have n_le_m: "n < m" unfolding n_def using assms(2) by simp

  have "measure ?pmf {x. \<forall>k'<state_k \<sigma>. x (k', n)} = measure ?pmf (Pi ({..<state_k \<sigma>} \<times>{n}) (\<lambda>_. {True}))"
    by (intro measure_pmf_cong) auto
  also have "... = (\<Prod>j \<in> {..<state_k \<sigma>}\<times>{n}. measure coin_pmf {True})"
    using assms(3) n_le_m by (intro prob_prod_pmf' subsetI) auto
  also have "... = (1/2) ^ state_k \<sigma>" by (simp add:measure_pmf_single)
  also have "... = 1 / 2 ^ state_k \<sigma>" unfolding power_one_over by simp
  finally have "1 / 2 ^ state_k \<sigma> = measure ?pmf {x. \<forall>k'<state_k \<sigma>. x (k', n)}" by simp
  hence "bernoulli_pmf (1/2^state_k \<sigma>) = map_pmf (\<lambda>\<phi>. \<forall>k'<state_k \<sigma>. \<phi> (k', n)) ?pmf"
    by (intro bool_pmf_eqI) (simp add:pmf_map vimage_def)
  also have "... = ?to_pmf (map_rd (\<lambda>\<phi>. \<forall>k'<state_k \<sigma>. \<phi> (k', n)) get_rd)"
    by (intro map_pmf_cong refl) (simp add:run_reader_simps)
  finally have a: "?to_pmf (map_rd (\<lambda>\<phi>. \<forall>k'<state_k \<sigma>. \<phi> (k', n)) get_rd) = bernoulli_pmf (1/2^state_k \<sigma>)"
    by simp

  have step_1: "?to_pmf (eager_step_1 (xs@[x]) n \<sigma>) = lazy_step_1 (xs@[x]) n \<sigma>"
    unfolding eager_step_1_def Let_def lazy_step_1_def by (subst lazify_bind_return) (simp_all add:a)

  have step_2: "?to_pmf (eager_step_2 (xs@[x]) n \<sigma>') = lazy_step_2 (xs@[x]) n \<sigma>'" (is "?L1 = ?R1")
    if "state_chi \<sigma>' \<subseteq> insert x (state_chi \<sigma>)" "state_k \<sigma>' = state_k \<sigma>" for \<sigma>'
  proof (cases "real (card (state_chi \<sigma>')) < threshold")
    case True
    then show ?thesis unfolding eager_step_2_def lazy_step_2_def by (simp add:lazify_return)
  next
    case False
    let ?f = "\<lambda>i. (state_k \<sigma>', find_last_before n i (xs @ [x]))"

    have b: "?f ` state_chi \<sigma>' \<subseteq> {..<m} \<times> {..<m}" using that(2) assms(3)
      by (intro image_subsetI) (auto intro!:dual_order.strict_trans2[OF n_le_m] find_last_before_bound)

    have "inj_on (\<lambda>i. find_last i (xs @ [x])) (set (xs @ [x]))" by (intro find_last_inj)
    hence "inj_on (\<lambda>i. find_last_before n i (xs @ [x])) (set (xs @ [x]))"
      unfolding find_last_before_def n_def by (simp add:find_last_inj)
    moreover have "inj (\<lambda>i. (state_k \<sigma>',i))" by (intro inj_onI) auto
    ultimately have "inj_on ((\<lambda>i. (state_k \<sigma>',i)) \<circ> (\<lambda>i. find_last_before n i (xs@[x]))) (set (xs@[x]))"
      using inj_on_subset by (intro comp_inj_on) force+
    hence "inj_on ?f (set (xs@[x]))" unfolding comp_def by simp
    moreover have "state_chi \<sigma>' \<subseteq> set (xs@[x])" using assms(4) that by auto
    ultimately have c:"inj_on ?f (state_chi \<sigma>')" using inj_on_subset by blast

    have "?to_pmf (map_rd (\<lambda>\<phi>. \<lambda>i\<in>state_chi \<sigma>'. \<phi> (?f i)) get_rd) = map_pmf (\<lambda>\<phi>. \<lambda>i\<in>state_chi \<sigma>'. \<phi> (?f i)) ?pmf"
      by (intro map_pmf_cong refl) (simp add:run_reader_simps)
    also have "... = prod_pmf (state_chi \<sigma>') ((\<lambda>_. coin_pmf) \<circ> ?f)"
      by (intro prod_pmf_reindex b c) auto
    also have "... = prod_pmf (state_chi \<sigma>') (\<lambda>_. coin_pmf)" by (simp add:comp_def)
    finally have "?to_pmf (map_rd (\<lambda>\<phi>. \<lambda>i\<in>state_chi \<sigma>'. \<phi> (?f i)) get_rd) = prod_pmf (state_chi \<sigma>') (\<lambda>_. coin_pmf)"
      by simp
    thus ?thesis unfolding eager_step_2_def Let_def  using False
      by (simp add:eager_step_2_def Let_def lazify_bind_return lazy_step_2_def)
  qed

  have "?L = ?to_pmf (eager_step_1 (xs@[x]) n \<sigma>) \<bind> (\<lambda>\<sigma>'. ?to_pmf (eager_step_2 (xs@[x]) n \<sigma>'))"
    unfolding eager_step_split n_def by (intro lazify_bind independent_bind_step) auto
  also have "... = lazy_step_1 (xs@[x]) n \<sigma> \<bind> (\<lambda>\<sigma>'. ?to_pmf (eager_step_2 (xs@[x]) n \<sigma>'))"
    unfolding step_1 by simp
  also have "... = lazy_step_1 (xs@[x]) n \<sigma> \<bind> lazy_step_2 (xs@[x]) n"
    by (intro bind_pmf_cong refl step_2)
      (auto simp add:lazy_step_1_def nth_append n_def cong:if_cong split:if_split_asm)
  also have "... = ?R" unfolding lazy_step_split by simp
  finally show ?thesis by simp
qed

lemma depends_on_step_approx:
  fixes xs
  defines "n \<equiv> length xs"
  shows "depends_on (eager_step (xs @ [x]) n \<sigma>) ({state_k \<sigma>..<state_k \<sigma>+1}\<times>{..<n+1} \<union> {..<state_k \<sigma>}\<times>{n})"
proof -
  have a:"state_k (run_reader (eager_step_1 (xs @ [x]) (length xs) \<sigma>) \<phi>) = state_k \<sigma>" for \<phi>
    unfolding eager_step_1_def by (simp add:run_reader_simps)

  show ?thesis
  unfolding eager_step_split n_def
    by (intro depends_on_bind depends_on_mono[OF depends_on_step1] depends_on_mono[OF depends_on_step2] )
      (auto simp add:a)
qed

lemma depends_on_step:
  fixes xs
  defines "n \<equiv> length xs"
  shows "depends_on (map_rd ((=) v) (eager_step (xs @ [x]) n \<sigma>)) ({state_k \<sigma>..<state_k v}\<times>{..<n+1} \<union> {..<state_k \<sigma>}\<times>{n})"
proof -
  show ?thesis unfolding n_def eager_step_split
  proof (intro depends_on_bind_eq conjI)
    fix w
    assume a:"w \<in> ran_rd (eager_step_1 (xs @ [x]) (length xs) \<sigma>)"
    assume "v \<in> ran_rd (eager_step_2 (xs @ [x]) (length xs) w)"

    show "depends_on (map_rd ((=) w) (eager_step_1 (xs @ [x]) (length xs) \<sigma>))
          ({state_k \<sigma>..<state_k v} \<times> {..<length xs + 1} \<union> {..<state_k \<sigma>} \<times> {length xs})"
      unfolding map_rd_def
      by (intro depends_on_bind depends_on_mono[OF depends_on_step1] depends_on_return) auto

    have "state_k \<sigma> = state_k w"
      using a unfolding ran_rd_def eager_step_1_def by (auto simp:run_reader_simps)
    thus "depends_on (map_rd ((=) v) (eager_step_2 (xs @ [x]) (length xs) w))
          ({state_k \<sigma>..<state_k v} \<times> {..<length xs + 1} \<union> {..<state_k \<sigma>} \<times> {length xs})"
      by (intro depends_on_mono[OF depends_on_step2_eq]) auto
  qed
qed

lemma depends_on_algorithm:
   "depends_on (map_rd ((=) v) (eager_algorithm xs)) ({..<state_k v} \<times> {..<length xs})"
proof (induction xs arbitrary:v rule:rev_induct)
  case Nil
  then show ?case by (simp add:eager_algorithm_def depends_on_return map_rd_def depends_on_bind)
next
  case (snoc x xs)
  show ?case
    unfolding eager_algorithm_snoc
  proof (intro depends_on_bind_eq conjI)
    fix w
    assume "w \<in> ran_rd (eager_algorithm xs)"
    assume "v \<in> ran_rd (eager_step (xs @ [x]) (length xs) w)"

    hence a: "state_k w \<le> state_k v"
      unfolding ran_rd_def by (auto simp:Let_def run_reader_simps eager_step_def)

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

text \<open>Convert between the algorithms\<close>

lemma lazy_step_eq_aux :
  \<open>lazy_step xs index = lazy_step (dummies @ xs) (length dummies + index)\<close>
proof -
  have \<open>(xs @ ys) ! (length xs + index) = ys ! index\<close> for xs ys index by simp

  then show ?thesis unfolding lazy_step_def by metis
qed

lemma lazy_algorithm_eq_aux :
  \<open>foldM_pmf (lazy_step xs) [0 ..< length xs] = foldM_pmf step_no_fail xs\<close>
proof -
  show ?thesis when \<open>\<And> dummies.
    foldM_pmf (lazy_step <| dummies @ xs) [length dummies ..< length dummies + length xs]
      = foldM_pmf step_no_fail xs\<close>
    (is \<open>\<And> offset y. ?thesis offset y\<close>)
    using that[of \<open>[]\<close>] by auto

  show \<open>?thesis dummies\<close> for dummies
  proof (induction xs arbitrary: dummies)
    case Nil
    then show ?case by simp
  next
    case (Cons x xs)

    then show ?thesis
      sorry

    (* have * :
      \<open>[offset ..< offset + length (x # xs)] 
        = offset # [Suc offset ..< Suc offset + length xs]\<close>
      sorry

    show ?case
      apply (rule ext)
      using Cons[of \<open>Suc offset\<close> dummy]
      apply (subst * )
      apply (simp only: foldM.simps)
      apply (auto simp del: List.upt.upt_Suc)
      sorry *)
  qed

  (* have \<open>lazy_step xs = ?step_no_fail\<close>
    by (fastforce
      intro: map_pmf_cong bind_pmf_cong
      simp add: lazy_step_def step_no_fail_def Let_def map_pmf_def[symmetric])
  
  then have
    \<open>foldM_pmf step_no_fail xs
      = foldM_pmf (\<lambda> n. ?step_no_fail (n - offset)) [offset ..< offset + length xs]\<close>
    for offset
    proof (induction xs arbitrary: offset)
      case Nil
      then show ?case by auto
    next
      case (Cons x xs)
      then show ?case sorry
    qed *)
qed

lemma lazy_algorithm_eq:
  shows "lazy_algorithm xs = run_steps_no_fail initial_state xs"
  by (simp add: lazy_algorithm_def lazy_algorithm_eq_aux run_steps_no_fail_def)

lemma
  "length xs \<le> n \<Longrightarrow>
  map_pmf (run_reader (eager_algorithm xs)) (prod_pmf ({..<n}\<times>{..<n}) (\<lambda>_. coin_pmf)) = lazy_algorithm xs"
proof (induction xs rule:rev_induct)
  case Nil
  then show ?case by (simp add:eager_algorithm_def return_rd_def lazy_algorithm_def)
next
  case (snoc x xs)
  let ?pmf = "prod_pmf ({..<n}\<times>{..<n}) (\<lambda>_. coin_pmf)"
  let ?to_pmf = "\<lambda>f. map_pmf (run_reader f) ?pmf"

  have a: "[0..<length (xs @ [x])] = [0..<length xs]@[length xs]" by simp
  have b: "length xs \<le> n" using snoc by simp

  have "?to_pmf (eager_algorithm (xs@[x])) = ?to_pmf (eager_algorithm xs \<bind> eager_step (xs @ [x]) (length xs))"
    unfolding eager_algorithm_snoc by simp
  also have "... = lazy_algorithm xs \<bind> (\<lambda>r. ?to_pmf (eager_step (xs@[x]) (length xs) r))"
    unfolding snoc(1)[OF b, symmetric] by (intro lazify_bind independent_bind) auto
  also have "... = lazy_algorithm xs \<bind> lazy_step (xs@[x]) (length xs)"
    using state_k_bound state_chi_bound snoc(2) by (intro bind_pmf_cong refl eager_lazy_step snoc(2)) fastforce
  also have "... = lazy_algorithm (xs@[x])"
    unfolding lazy_algorithm_snoc by simp
  finally show ?case by simp
qed

end

end