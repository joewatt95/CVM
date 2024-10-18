theory Utils_List

imports
  "HOL-Probability.SPMF"
  CVM.Utils_Function
  CVM.Utils_Option

begin

definition least_index :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> nat option\<close> where
  \<open>least_index xs x \<equiv>
    if x \<in> set xs
    then Some <| LEAST index. xs ! index = x
    else None\<close>

lemma least_index_le_length :
  assumes \<open>least_index xs x = Some index\<close>
  shows \<open>index < length xs\<close>
  by (metis (mono_tags, lifting) assms in_set_conv_nth least_index_def linorder_less_linear not_less_Least option.discI option.inject order_less_trans)

lemma least_index_take_mono :
  fixes xs x i j
  assumes \<open>i \<le> j\<close>
  defines
    \<open>least_index_up_to index \<equiv> least_index (take index xs) x\<close>
  shows \<open>ord_option (\<le>) (least_index_up_to i) (least_index_up_to j)\<close>
  using assms
  apply (simp add: least_index_def)
  by (smt (verit, best) LeastI2 in_set_conv_nth length_take linorder_not_less min_less_iff_conj not_less_Least nth_take order.trans) 

lemma least_index_eq_of_index_le :
  fixes xs x i j
  assumes \<open>i \<le> j\<close> \<open>x \<in> set (take i xs)\<close> 
  defines
    \<open>least_index_up_to index \<equiv> least_index (take index xs) x\<close>
  shows \<open>least_index_up_to i = least_index_up_to j\<close>
proof -
  have \<open>ord_option (\<le>) (least_index_up_to i) (least_index_up_to j)\<close>
    by (simp add: assms(1) least_index_take_mono least_index_up_to_def) 

  then show ?thesis
    using assms
    apply (simp add: least_index_def)
    by (smt (verit) LeastI in_set_conv_nth length_take linorder_less_linear linorder_not_less min_less_iff_conj not_less_Least nth_take ord_option_simps(3) order.strict_trans2) 
qed

lemma least_index_eq_of_Suc_index :
  fixes xs x i
  assumes \<open>x \<in> set (take i xs)\<close> 
  defines
    \<open>least_index_up_to index \<equiv> least_index (take index xs) x\<close>
  shows \<open>least_index_up_to (Suc i) = least_index_up_to i\<close>
  by (metis assms least_index_eq_of_index_le lessI less_imp_le_nat) 

definition greatest_index :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> nat option\<close> where
  \<open>greatest_index xs x = (
    if x \<in> set xs
    then Some <| GREATEST index. xs ! index = x
    else None)\<close>

(* lemma greatest_index_take_mono :
  fixes xs x i j
  assumes \<open>i \<le> j\<close> \<open>j < length xs\<close>
  defines
    \<open>greatest_index_up_to index \<equiv> greatest_index (take index xs) x\<close>
  shows
    \<open>ord_option (\<le>) (greatest_index_up_to i) (greatest_index_up_to j)\<close>
    (is \<open>_ _ ?L ?R\<close>)
  using assms
  apply (auto simp add: greatest_index_def)

  prefer 2
  apply (meson set_take_subset_set_take subsetD)

  sorry *)

(* lemma
  \<open>(GREATEST index. (xs @ [x]) ! index = x) = length xs\<close>
  apply (rule GreatestI2_order[where x = \<open>length xs\<close>])

  subgoal by simp

  subgoal premises prems for index
    proof (rule classical)
      assume \<open>\<not> index \<le> length xs\<close>

      then have \<open>index > length xs\<close> by simp

      then have False
        using prems
        sorry

      then show ?thesis by blast
    qed

  sorry *)

(* lemma greatest_index_altdef :
  \<open>greatest_index xs x = (
    xs
      |> rev
      |> (flip least_index x)
      |> map_option (\<lambda> least_index. length xs - Suc least_index))\<close>
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case
    by (auto simp add: greatest_index_def least_index_def)
next
  case (snoc y xs)

  then show ?case
    apply (auto simp add: least_index_def greatest_index_def)
    sorry
qed *)

(* lemma
  assumes \<open>i < length xs\<close>
  shows \<open>greatest_index (take (Suc i) xs) (xs ! i) = Some i\<close>

  using assms
  apply (auto simp add: greatest_index_def)

  prefer 2
  apply (simp add: take_Suc_conv_app_nth)
  
  sledgehammer

  sorry *)

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

lemma find_last_before_self_eq:
  assumes "i < length xs"
  shows "find_last_before i (xs ! i) xs = i"
  unfolding find_last_before_def find_last_def Let_def
  using assms by auto

end