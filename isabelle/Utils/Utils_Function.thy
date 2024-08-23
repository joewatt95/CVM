theory Utils_Function

imports
  Main

begin

definition flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c" where
  [simp] : "flip f x y \<equiv> f y x"

definition pipe :: "'a \<Rightarrow>('a \<Rightarrow> 'b) \<Rightarrow> 'b" (infixl "|>" 0) where
  [simp] : "(|>) \<equiv> flip id"

definition app :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" (infixr "<|" 0) where
  [simp] : "(<|) \<equiv> id"

end