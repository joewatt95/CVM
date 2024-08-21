theory Utils_Function

imports
  Main

begin

abbreviation flip :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c" where
  "flip f x y \<equiv> f y x"

abbreviation pipe :: "'a \<Rightarrow>('a \<Rightarrow> 'b) \<Rightarrow> 'b" (infixl "|>" 0) where
  "(|>) \<equiv> flip id"

end