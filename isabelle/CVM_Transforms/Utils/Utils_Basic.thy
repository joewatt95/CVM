section \<open>Basic utilities\<close>

text
  \<open>This provides basic, general utilities that are used throughout the rest
  of this development.\<close>

theory Utils_Basic

imports
  "HOL-Library.Monad_Syntax"

begin

abbreviation (input) flip :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c\<close> where
  \<open>flip \<equiv> \<lambda> f x y. f y x\<close>

abbreviation (input) app :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b\<close>
  (infixr \<open><|\<close> 0) where
  \<open>(<|) \<equiv> (\<lambda> f. f)\<close>

abbreviation (input) pipe :: \<open>'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b\<close>
  (infixl \<open>|>\<close> 0) where
  \<open>(|>) \<equiv> flip (<|)\<close>

abbreviation (input) comp_left :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c\<close>
  (infixl \<open><<<\<close> 55) where
  \<open>(g <<< f) \<equiv> (\<lambda> x. g (f x))\<close>

abbreviation (input) comp_right :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'c\<close>
  (infixl \<open>>>>\<close> 55) where
  \<open>(f >>> g) \<equiv> g <<< f\<close>

abbreviation (input) constantly
  (\<open>\<lblot> _ \<rblot>\<close> 1000) where
  \<open>\<lblot>x\<rblot> \<equiv> \<lambda> _. x\<close>

abbreviation (input) \<open>uncurry \<equiv> case_prod\<close>

abbreviation is_None_or_pred :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>is_None_or_pred \<equiv> case_option True\<close>

abbreviation is_Some_and_pred :: \<open>('a \<Rightarrow> bool) \<Rightarrow> 'a option \<Rightarrow> bool\<close> where
  \<open>is_Some_and_pred \<equiv> case_option False\<close>

lemma finset_card_filter_eq_iff_Ball :
  assumes \<open>finite A\<close>
  shows \<open>card (Set.filter P A) = card A \<longleftrightarrow> Ball A P\<close>
  using assms
  apply simp
  by (metis (no_types, lifting) card_subset_eq mem_Collect_eq subsetI subset_antisym)

lemma take_length_eq_self :
  \<open>take (length xs) (xs @ ys) = xs\<close>
  by simp

syntax
  "_flip_bind" :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'b\<close>
  (infixl \<open>=<<\<close> 54)
  "_kleisli_comp_right" :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'c\<close>
  (infixl \<open>>=>\<close> 50)
  "_kleisli_comp_left" :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c\<close>
  (infixr \<open><=<\<close> 50)

syntax_consts
  "_flip_bind" "_kleisli_comp_right" "_kleisli_comp_left" \<rightleftharpoons> Monad_Syntax.bind

translations
  "_flip_bind" \<rightharpoonup> "CONST flip Monad_Syntax.bind"
  "_kleisli_comp_right f g" \<rightharpoonup> "f >>> (=<<) g"
  "_kleisli_comp_left f g" \<rightharpoonup> "g >=> f"

context
  fixes
    bind :: \<open>'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c\<close> and
    return :: \<open>'b \<Rightarrow> 'c\<close>
begin

fun foldM :: \<open>('d \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'd list \<Rightarrow> 'b \<Rightarrow> 'c\<close> where
  \<open>foldM _ [] = return\<close> |
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
  unfolding foldM_enumerate_def
  apply (induction xs arbitrary: offset) by simp_all

end

end