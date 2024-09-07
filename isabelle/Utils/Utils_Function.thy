theory Utils_Function

imports
  Main
  (* "HOL-Library.Monad_Syntax" *)

begin

definition flip :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c\<close> where
  [simp] : \<open>flip f x y \<equiv> f y x\<close>

definition pipe :: \<open>'a \<Rightarrow>('a \<Rightarrow> 'b) \<Rightarrow> 'b\<close> (infixl \<open>|>\<close> 0) where
  [simp] : \<open>(|>) \<equiv> flip id\<close>

definition app :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b\<close> (infixr \<open><|\<close> 0) where
  [simp] : \<open>(<|) \<equiv> id\<close>

definition comp_left :: \<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c\<close>
  (infixl \<open><<<\<close> 55) where
  [simp] : \<open>(g <<< f) \<equiv> (\<lambda> x. g (f x))\<close>

definition comp_right :: \<open>('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'c\<close>
  (infixl \<open>>>>\<close> 55) where
  [simp] : \<open>(f >>> g) \<equiv> (\<lambda> x. g (f x))\<close>

end