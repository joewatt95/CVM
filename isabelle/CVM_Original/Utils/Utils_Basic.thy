theory Utils_Basic

imports
  "List-Index.List_Index"

begin

abbreviation (input) flip :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c\<close> where
  \<open>flip f x y \<equiv> f y x\<close>

abbreviation (input) app :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b\<close>
  (infixr \<open><|\<close> 0) where
  \<open>(<|) f \<equiv> f\<close>

abbreviation (input) pipe :: \<open>'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b\<close>
  (infixl \<open>|>\<close> 0) where
  \<open>(|>) \<equiv> flip (<|)\<close>

abbreviation (input) comp_left :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c\<close>
  (infixl \<open><<<\<close> 55) where
  \<open>(g <<< f) \<equiv> (\<lambda> x. g (f x))\<close>

abbreviation (input) comp_right :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'c\<close>
  (infixl \<open>>>>\<close> 55) where
  \<open>(f >>> g) \<equiv> (\<lambda> x. g (f x))\<close>

abbreviation (input) constantly
  (\<open>\<lblot> _ \<rblot>\<close> 1000) where
  \<open>\<lblot>x\<rblot> \<equiv> \<lambda> _. x\<close>

abbreviation (input) uncurry :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c\<close> where
  \<open>uncurry f \<equiv> \<lambda> (a, b). f a b\<close>

definition map_index :: \<open>(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list\<close> where
  \<open>map_index f \<equiv> map (uncurry f) <<< enumerate 0\<close>

lemma finset_card_filter_eq_iff_Ball :
  assumes \<open>finite A\<close>
  shows \<open>card (Set.filter P A) = card A \<longleftrightarrow> Ball A P\<close>
  using assms
  by (metis card_seteq dual_order.refl member_filter subsetI subset_antisym)

context
  fixes
    bind :: \<open>'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c\<close> and
    return :: \<open>'b \<Rightarrow> 'c\<close>
begin

fun foldM ::
  \<open>('d \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'd list \<Rightarrow> 'b \<Rightarrow> 'c\<close> where
  \<open>foldM  _ [] = return\<close> |
  \<open>foldM f (x # xs) = (\<lambda> val. bind (f x val) (foldM f xs))\<close>

lemma foldM_cong:
  assumes \<open>\<And> x. x \<in> set xs \<Longrightarrow> f x = f' x\<close>
  shows \<open>foldM f xs v = foldM f' xs v\<close>
using assms proof (induction xs arbitrary: v)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp_all presburger
qed

definition
  \<open>foldM_enumerate \<equiv> \<lambda> f xs offset. foldM f (List.enumerate offset xs)\<close>

lemma foldM_eq_foldM_enumerate :
  \<open>foldM f xs = foldM_enumerate (f <<< snd) xs offset\<close>
  apply (induction xs arbitrary: offset)
  unfolding foldM_enumerate_def by simp_all

end

definition last_index_up_to :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> nat\<close> where
  \<open>last_index_up_to \<equiv> \<lambda> k. last_index <<< take (Suc k)\<close>

lemma last_index_up_to_le :
  \<open>last_index_up_to n xs x \<le> Suc n\<close>
  unfolding last_index_up_to_def
  by (metis cancel_comm_monoid_add_class.diff_cancel drop_eq_Nil drop_take dual_order.trans last_index_le_size take0)

context
  fixes i xs
  assumes \<open>i < length xs\<close>
begin

lemma last_index_up_to_self_eq :
  \<open>last_index_up_to i xs (xs ! i) = i\<close>
  using \<open>i < length xs\<close>
  unfolding last_index_up_to_def
  by (simp add: take_Suc_conv_app_nth)

lemma find_last_before_eq_find_last_iff :
  assumes \<open>x \<in> set (take i xs)\<close>
  shows
    \<open>last_index_up_to i xs x = last_index (take i xs) x
    \<longleftrightarrow> x \<noteq> xs ! i\<close>
  using assms \<open>i < length xs\<close>
  unfolding last_index_up_to_def
  by (metis last_index_Snoc last_index_less_size_conv less_not_refl take_Suc_conv_app_nth)

end

end