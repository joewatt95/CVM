section \<open>Preliminary Definitions\<close>

theory Utils_Basic
  imports Main
begin

fun foldM ::
  \<open>('a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'd list \<Rightarrow> 'b \<Rightarrow> 'c\<close> where
  \<open>foldM _ return _ [] val = return val\<close> |
  \<open>foldM bind return f (x # xs) val =
    bind (f x val) (foldM bind return f xs)\<close>

lemma foldM_cong:
  assumes "\<And> x. x \<in> set xs \<Longrightarrow> f x = f' x"
  shows "foldM bind return f xs v = foldM bind return f' xs v"
  using assms
proof (induction xs arbitrary: v)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by simp_all presburger
qed

lemma foldM_empty: "foldM bind return f [] = return" by auto

end