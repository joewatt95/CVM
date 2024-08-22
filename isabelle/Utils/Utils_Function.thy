theory Utils_Function

imports
  Main

begin

definition flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c" where
  "flip f x y = f y x"

definition pipe :: "'a \<Rightarrow>('a \<Rightarrow> 'b) \<Rightarrow> 'b" (infixl "|>" 0) where
  "(|>) = flip id"

end