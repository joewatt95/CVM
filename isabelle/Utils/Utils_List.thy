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

lemma find_last_eq_of :
  assumes
    \<open>i < length xs\<close>
    \<open>xs ! i = x\<close>
    \<open>x \<notin> set (nths xs {i + 1 ..< length xs})\<close>
  shows \<open>find_last x xs = i\<close>
proof -
  have \<open>\<not> find_last x xs < i\<close>
    using assms find_last_correct_1(3) nth_mem by (fastforce simp add: set_nths)

  moreover have \<open>\<not> find_last x xs > i\<close>
    using assms
    apply (simp add: set_nths)
    by (metis Suc_leI find_last_correct_1(1) find_last_correct_1(2) nth_mem)

  ultimately show ?thesis using nat_neq_iff by blast
qed

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

lemma find_last_before_eq_find_last_of :
  assumes
    \<open>i < length xs\<close>
    \<open>x \<noteq> xs ! i\<close>
    \<open>x \<in> set (take i xs)\<close>
  shows
    \<open>find_last_before i x xs = find_last x (take i xs)\<close> (is \<open>?last_index = _\<close>)
proof -
  have \<open>?last_index < i\<close>
    by (metis assms in_set_take_conv_nth Nat.add_0_right Suc_eq_plus1 find_last_before_bound find_last_before_def find_last_correct_1(1) find_last_correct_2 le_antisym lessI less_imp_le_nat linorder_neqE_nat nat_add_left_cancel_less not_add_less1 nth_take)

  moreover have
    \<open>xs ! ?last_index = x\<close>
    using calculation
    apply (simp add: set_nths find_last_before_def)
    by (smt (verit) assms find_last_correct_1(1) in_set_take_conv_nth le_antisym le_refl nat_less_le nat_neq_iff not_less_eq nth_mem nth_take take_all)

  moreover have
    \<open>x \<noteq> xs ! j\<close>
    if \<open>find_last_before i x xs + 1 \<le> j\<close> \<open>j < i\<close> for j
    using assms that find_last_correct_1(3)[of _ \<open>take (i + 1) xs\<close>]
    apply (simp add: set_nths find_last_before_def)
    by (metis Suc_le_eq butlast_take diff_Suc_1 in_set_butlastD le_imp_less_Suc less_or_eq_imp_le nth_take)

  ultimately show ?thesis
    using assms
    by (fastforce intro: find_last_eq_of[symmetric] simp add: set_nths)
qed

end