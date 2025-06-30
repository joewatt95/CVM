theory Utils_Option

imports
  Main

begin

abbreviation is_some :: \<open>'a option \<Rightarrow> bool\<close> where
  \<open>is_some \<equiv> (\<noteq>) None\<close>

instantiation option :: (type) zero
begin
  definition zero where
    \<open>zero \<equiv> None\<close>
  
  instance ..
end

end