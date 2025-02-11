section \<open> Definition of the CVM algorithm \<close>
theory CVM_Algo

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Utils_SPMF_FoldM_Hoare

begin

record 'a state =
  state_k :: nat
  state_chi :: \<open>'a set\<close>

definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> \<lparr>state_k = 0, state_chi = {}\<rparr>\<close>

locale cvm_algo =
  fixes threshold :: nat
begin

abbreviation f :: real where \<open>f \<equiv> 1 / 2\<close>

definition compute_estimate :: \<open>'a state \<Rightarrow> real\<close> where
  \<open>compute_estimate \<equiv> \<lambda> state. card (state_chi state) / f ^ (state_k state)\<close>

text
  \<open>The algorithm is defined in the SPMF monad (with None representing failure)\<close>

definition step_1 :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_1 \<equiv> \<lambda> x state. do {
    let k = state_k state; let chi = state_chi state;
    insert_x_into_chi \<leftarrow> bernoulli_pmf <| f ^ k;
    let chi = (chi |>
      if insert_x_into_chi
      then insert x
      else Set.remove x);
    return_pmf (state\<lparr>state_chi := chi\<rparr>) }\<close>

definition step_2 :: \<open>'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_2 \<equiv> \<lambda> state.
    let k = state_k state; chi = state_chi state
    in if card chi = threshold
      then do {
        keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow> prod_pmf chi \<lblot>bernoulli_pmf f\<rblot>;
        return_pmf (\<lparr>state_k = k + 1, state_chi = Set.filter keep_in_chi chi\<rparr>) }
      else return_pmf state\<close>

definition step_3 :: \<open>'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step_3 \<equiv> \<lambda> state.
    if card (state_chi state) = threshold
    then fail_spmf
    else return_spmf state\<close>

definition step :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step \<equiv> \<lambda> x state. spmf_of_pmf (step_1 x state \<bind> step_2) \<bind> step_3\<close>

abbreviation \<open>run_steps \<equiv> foldM_spmf step\<close>

abbreviation
  \<open>cvm xs \<equiv> map_spmf compute_estimate (foldM_spmf step xs initial_state)\<close>

lemmas step_1_def' =
  step_1_def[simplified map_pmf_def[symmetric] Let_def if_distribR]

lemmas step_2_def' =
  step_2_def[simplified map_pmf_def[symmetric] Let_def]

end

locale cvm_algo_assms = cvm_algo + ord_spmf_syntax +
  assumes threshold : \<open>threshold > 0\<close>

end
