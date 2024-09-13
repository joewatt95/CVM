theory Utils_SPMF_Common

imports
  "HOL-Probability.SPMF"
  CVM.Utils_Function

begin

definition fail_spmf :: \<open>'a spmf\<close> where
  \<open>fail_spmf \<equiv> return_pmf None\<close>

definition prob_fail :: \<open>'a spmf \<Rightarrow> real\<close> where
  \<open>prob_fail \<equiv> flip pmf None\<close>

definition kleisli_compose_left ::
  \<open>('a \<Rightarrow> 'b spmf) \<Rightarrow> ('b \<Rightarrow> 'c spmf) \<Rightarrow> 'a \<Rightarrow> 'c spmf\<close>
  (infixl \<open>>=>\<close> 50) where
  \<open>(f >=> g) \<equiv> \<lambda> x. bind_spmf (f x) g\<close>

definition kleisli_compose_right (infixr \<open><=<\<close> 50) where
  \<open>(f <=< g) \<equiv> g >=> f\<close>

end