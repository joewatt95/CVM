theory Algo_Transforms_Lazy

imports
  CVM.Utils_List
  CVM.Utils_Reader_Monad_Basic
  CVM.Utils_PMF_Bernoulli_Binomial
  CVM.Algo_Transforms_No_Fail

begin

context with_threshold_pos
begin

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

definition lazy_step :: "'a list \<Rightarrow> nat \<Rightarrow> 'a state \<Rightarrow> 'a state pmf"
  where "lazy_step xs i state = lazy_step_1 xs i state \<bind> lazy_step_2 xs i"

definition
  \<open>run_steps_from_state fold_fn step_fn state xs \<equiv>
    fold_fn (step_fn xs) [0 ..< length xs] state\<close>

definition lazy_algorithm :: "'a list \<Rightarrow> 'a state pmf"  where
  "lazy_algorithm \<equiv> run_steps_from_state foldM_pmf lazy_step initial_state"

lemma lazy_step_cong:
  assumes "xs ! i = ys ! i"
  shows "lazy_step xs i = lazy_step ys i"
  unfolding lazy_step_def lazy_step_1_def lazy_step_2_def
  using assms by (simp cong: if_cong)

lemma lazy_algorithm_snoc:
  "lazy_algorithm (xs@[x]) = lazy_algorithm xs \<bind> lazy_step (xs@[x]) (length xs)"
proof -
  have a: "[0..<length (xs @ [x])] = [0..<length xs]@[length xs]" by simp

  show ?thesis
    unfolding lazy_algorithm_def run_steps_from_state_def a foldM_pmf_snoc
    by (intro foldM_cong bind_pmf_cong refl lazy_step_cong) (auto simp:nth_append)
qed

lemma state_k_bound:
  assumes "\<omega> \<in> set_pmf (lazy_algorithm xs)"
  shows "state_k \<omega> \<le> length xs"
  using assms
proof (induction xs arbitrary:\<omega> rule:rev_induct)
  case Nil
  then show ?case unfolding lazy_algorithm_def run_steps_from_state_def initial_state_def by simp
next
  case (snoc x xs)
  let ?n = "length xs"

  obtain \<omega>1 \<omega>2 where \<omega>:
    "\<omega>1 \<in> set_pmf (lazy_algorithm xs)"
    "\<omega>2 \<in> set_pmf (lazy_step_1 (xs@[x]) ?n \<omega>1)"
    "\<omega> \<in> set_pmf (lazy_step_2 (xs@[x]) ?n \<omega>2)"
    using snoc unfolding lazy_algorithm_snoc lazy_step_def by auto

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
  then show ?case unfolding lazy_algorithm_def run_steps_from_state_def initial_state_def by simp
next
  case (snoc x xs)
  let ?n = "length xs"

  obtain \<omega>1 \<omega>2 where \<omega>:
    "\<omega>1 \<in> set_pmf (lazy_algorithm xs)"
    "\<omega>2 \<in> set_pmf (lazy_step_1 (xs@[x]) ?n \<omega>1)"
    "\<omega> \<in> set_pmf (lazy_step_2 (xs@[x]) ?n \<omega>2)"
    using snoc unfolding lazy_algorithm_snoc lazy_step_def by auto

  have "state_chi \<omega>1 \<subseteq> set xs" using snoc \<omega>(1) by simp
  moreover have "state_chi \<omega>2 \<subseteq> insert x (state_chi \<omega>1)"
    using \<omega>(2) unfolding lazy_step_1_def
    by (auto simp add:nth_append cong:if_cong split:if_split_asm)
  ultimately have "state_chi \<omega>2 \<subseteq> set (xs@[x])" by auto
  hence "state_chi \<omega> \<subseteq> set (xs@[x])" using \<omega>(3) unfolding lazy_step_2_def
    by (cases "real (card (state_chi \<omega>2)) < threshold") (auto simp:Let_def)
  thus ?case by simp
qed

(* lemma lazy_algorithm_eq_snoc_version:
  \<open>lazy_algorithm xs = run_steps_pmf step_no_fail xs\<close>
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case unfolding run_steps_from_state_def run_steps_def by simp
next
  case (snoc x xs)

  have step:"lazy_step (xs @ [x]) (length xs) = step_no_fail x"
    unfolding lazy_step_def step_no_fail_def Let_def
    by (intro ext bind_pmf_cong refl) (simp add:nth_append)

  show ?case
    unfolding lazy_algorithm_snoc snoc
    unfolding run_steps_def foldM_pmf_snoc step by simp
qed *)

lemma lazy_algorithm_eq_run_step_no_fail :
  \<open>lazy_algorithm xs = foldM_pmf step_no_fail xs initial_state\<close>
proof -
  (* As with proving things about `List.enumerate`, we need to introduce an
    arbitrary offset to the list of indices `[0 ..< length xs]` passed as input
    to the lhs.
    If not, our IH will be too weak, as it will talk about `[0 ..< length xs]`,
    but due to the structure of our fold, we instead want to rewrite and apply
    our IH to the following:
      `[0 ..< length xs + 1] = 0 # [1 ..< length xs + 1]`

    For this to work, we also need to pad the input list to `lazy_step` since
    it access elements in `xs` by indexing with the list of indices
    `[0 ..< length xs]`
  *)
  show ?thesis when \<open>\<And> padding.
    foldM_pmf
      (lazy_step <| padding @ xs)
      [length padding ..< length padding + length xs]
    = foldM_pmf step_no_fail xs\<close>
    (is \<open>\<And> padding. ?thesis padding\<close>)
    using that[of \<open>[]\<close>]
    by (auto simp add: lazy_algorithm_def run_steps_from_state_def)

  show \<open>?thesis padding\<close> for padding
  proof (induction xs arbitrary: padding)
    case Nil
    show ?case by simp
  next
    case (Cons x xs)

    note Cons.IH[of \<open>padding @ [x]\<close>]

    (* Think of `a` as `length xs` and `b` as `length padding` *)
    moreover have \<open>[a ..< a + (b + 1)] = a # [a + 1 ..< (a + 1) + b]\<close>
      for a b :: nat by (simp add: upt_rec)

    moreover have
      \<open>lazy_step (padding @ x # xs) (length padding) = step_no_fail x\<close>
      by (fastforce
        intro: bind_pmf_cong
        simp add:
          lazy_step_def lazy_step_1_def lazy_step_2_def step_no_fail_def
          map_bind_pmf bind_map_pmf map_pmf_def[symmetric] map_pmf_comp Let_def)

    ultimately show ?case by (auto cong: bind_pmf_cong)
  qed
qed

theorem estimate_distinct_no_fail_eq_lazy_algo :
  \<open>estimate_distinct_no_fail = lazy_algorithm >>> map_pmf compute_estimate\<close>
  unfolding estimate_distinct_no_fail_def run_steps_then_estimate_def lazy_algorithm_eq_run_step_no_fail ..

end

end