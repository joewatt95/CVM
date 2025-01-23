theory Utils_New

imports
  "HOL-Probability.SPMF"
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

abbreviation \<open>fail_spmf \<equiv> return_pmf None\<close>

abbreviation \<open>prob_fail \<equiv> flip pmf None\<close>

context
  fixes
    bind :: \<open>'a \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'c\<close> and
    return :: \<open>'b \<Rightarrow> 'c\<close>
begin

fun foldM ::
  \<open>('d \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'd list \<Rightarrow> 'b \<Rightarrow> 'c\<close> where
  \<open>foldM  _ [] = return\<close> |
  \<open>foldM f (x # xs) = (\<lambda> val. bind (f x val) (foldM f xs))\<close>

end

abbreviation foldM_pmf ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b pmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b pmf\<close> where
  \<open>foldM_pmf \<equiv> foldM bind_pmf return_pmf\<close>

abbreviation foldM_spmf ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b spmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b spmf\<close> where
  \<open>foldM_spmf \<equiv> foldM bind_spmf return_spmf\<close>

end