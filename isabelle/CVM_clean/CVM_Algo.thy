theory CVM_Algo
  imports
    Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
    Helper
begin

record 'a state =
  state_k :: nat
  state_chi :: \<open>'a set\<close>

locale cvm_algo =
  fixes n::nat
  fixes f::real
begin

definition step1 :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step1 x st \<equiv> do {
    let k = state_k st;
    let chi = state_chi st; 
    coin \<leftarrow> bernoulli_pmf (f ^ k);
    let chi =
      (if coin
      then insert x chi
      else Set.remove x chi);
    return_pmf \<lparr>state_k = k, state_chi = chi\<rparr>
  }\<close>

definition subsample :: "'a set \<Rightarrow> 'a set pmf" where
  \<open>subsample chi \<equiv>
    pmf_of_set { S . S \<subseteq> chi \<and> real (card S) = real n * f }\<close>

definition step2 :: \<open>'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step2 st \<equiv> do {
    let k = state_k st;
    let chi = state_chi st;
    if card chi = n then
    do {
      chi \<leftarrow> subsample chi;
      return_pmf \<lparr>state_k = k + 1, state_chi = chi\<rparr>
    }
    else
      return_pmf st
  }\<close>

definition cvm_step :: "'a \<Rightarrow> 'a state \<Rightarrow> 'a state pmf" where
  \<open>cvm_step x st \<equiv> step1 x st \<bind> step2\<close>

abbreviation foldM_pmf ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b pmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b pmf\<close> where
  \<open>foldM_pmf \<equiv> foldM bind_pmf return_pmf\<close>

definition cvm :: "'a list \<Rightarrow> 'a state \<Rightarrow> 'a state pmf" where
  \<open>cvm \<equiv> foldM_pmf cvm_step\<close>

end

end