theory Utils_List

imports
  "HOL-Probability.SPMF"
  CVM.Utils_Function
  CVM.Utils_Option

begin

lemma nonempty_iff_length_ge_1 :
  \<open>xs \<noteq> [] \<longleftrightarrow> length xs \<ge> 1\<close>
  by (simp add: Suc_le_eq)

lemma card_set_take_le_card_set :
  \<open>card (set (take i xs)) \<le> card (set xs)\<close>
  by (simp add: card_mono set_take_subset)

lemma insert_nth_set_take_eq_set_take_Suc :
  assumes \<open>i < length xs\<close>
  shows \<open>insert (xs ! i) (set (take i xs)) = set (take (Suc i) xs)\<close>
  using assms
  apply (induction xs rule: rev_induct)
  apply simp
  by (metis Un_insert_right append_Nil2 list.simps(15) set_append take_Suc_conv_app_nth)

lemma in_set_take_conv_nth :
  assumes \<open>i < length xs\<close>
  shows \<open>x \<in> set (take i xs) \<longleftrightarrow> (\<exists> j < i. xs ! j = x)\<close>
  by (auto simp add: assms in_set_conv_nth)

definition find_last :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
  where "find_last x xs = (
    let ps = filter (\<lambda>i. xs ! i = x) [0..<length xs]
    in (if ps = [] then 0 else (last ps)))"

lemma sorted_last_eq_Max:
  assumes "sorted ps" "ps \<noteq> []"
  shows "last ps = Max (set ps)"
proof -
  define a b where ab: "a = butlast ps" "b = last ps"
  have a:"ps = a@[b]" unfolding ab using assms(2) by simp
  have "b = Max (set ps)" using assms(1) unfolding a by (simp add: Max_insert2 sorted_append)
  thus ?thesis unfolding a by simp
qed

lemma find_last_correct_1:
  assumes "x \<in> set xs"
  shows "xs ! find_last x xs = x" "find_last x xs < length xs" "x \<notin> set (nths xs {find_last x xs+1..<length xs})"
proof -
  define ps where "ps = filter (\<lambda>i. xs ! i = x) [0..<length xs]"
  have ps_ne: "ps \<noteq> []" using assms unfolding ps_def filter_empty_conv in_set_conv_nth by auto

  have a:"find_last x xs = last ps" using ps_ne unfolding find_last_def ps_def[symmetric] by simp

  have "i < length xs" if "i \<in> set ps" for i using that unfolding ps_def by simp
  thus "find_last x xs < length xs" unfolding a using ps_ne last_in_set by simp

  have "xs ! i = x" if "i \<in> set ps" for i using that unfolding ps_def set_filter by simp
  thus "xs ! find_last x xs = x" unfolding a using ps_ne last_in_set by simp

  have "sorted ps" unfolding ps_def by (intro sorted_wrt_filter) simp
  hence "last ps = Max (set ps)" using sorted_last_eq_Max ps_ne by auto
  hence b:"i \<le> last ps" if "i \<in> set ps" for i using ps_ne that by simp

  show "x \<notin> set (nths xs {find_last x xs+1..<length xs})"
  proof (rule ccontr)
    assume "\<not> x \<notin> set (nths xs {find_last x xs + 1..<length xs})"
    then obtain i where "i \<in> {last ps + 1..<length xs}" "xs ! i = x"
      unfolding set_nths a by auto
    hence "i \<in> set ps" "last ps < i" unfolding ps_def by auto
    thus False using b by fastforce
  qed
qed

lemma find_last_correct_2:
  assumes "x \<notin> set xs"
  shows "find_last x xs = 0"
  using assms unfolding find_last_def Let_def filter_empty_conv in_set_conv_nth by auto

lemma find_last_inj:
  "inj_on (\<lambda>x. find_last x xs) (set xs)"
  by (intro inj_onI) (metis find_last_correct_1(1))

lemma find_last_eq_Max :
  \<open>find_last x xs = (
    if x \<in> set xs
    then Max {i \<in> {0 ..< length xs}. xs ! i = x}
    else 0)\<close>
  using find_last_correct_1[of x xs] find_last_correct_2[of x xs]
  by (auto intro: Max_eqI[symmetric] simp add: set_nths not_less_eq_eq)

definition find_last_before :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> nat"
  where "find_last_before k x xs = find_last x (take (k+1) xs)"

lemma find_last_before_bound:
  "find_last_before n x xs \<le> n"
proof (cases "x \<in> set (take (n+1) xs)")
  case True
  hence "find_last_before n  x xs < n+1"
    unfolding find_last_before_def using find_last_correct_1(2) by fastforce
  thus ?thesis by simp
next
  case False
  hence "find_last_before n x xs = 0"
    unfolding find_last_before_def using find_last_correct_2 by fastforce
  thus ?thesis by simp
qed

context
  fixes i xs
  assumes \<open>i < length xs\<close>
begin

lemma find_last_before_self_eq :
  \<open>find_last_before i (xs ! i) xs = i\<close>
  unfolding find_last_before_def find_last_def Let_def
  using \<open>i < length xs\<close> by auto

lemma find_last_before_eq_find_last_iff :
  assumes \<open>x \<in> set (take i xs)\<close>
  shows
    \<open>find_last_before i x xs = find_last x (take i xs)
    \<longleftrightarrow> x \<noteq> xs ! i\<close>
    (is \<open>?L \<longleftrightarrow> ?R\<close>)
proof -
  have ?L if ?R
    using assms that
    apply (simp add: find_last_before_def find_last_eq_Max) 
    by (smt (verit, ccfv_SIG) Collect_cong in_set_takeD in_set_take_conv_nth le_eq_less_or_eq less_Suc_eq linorder_neqE_nat nth_take take_all_iff)

  then show ?thesis
    using assms find_last_before_self_eq find_last_correct_1(2) by fastforce 
qed

end

end