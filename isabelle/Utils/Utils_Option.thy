theory Utils_Option

imports
  Main

begin

instantiation option :: (type) zero
begin
  definition zero where
    \<open>zero \<equiv> None\<close>
  
  instance ..
end

end