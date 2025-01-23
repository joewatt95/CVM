section \<open> TODO \<close>
theory Algo

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Utils_PMF_Basic
  Utils_SPMF_FoldM

begin

record 'a state =
  state_k :: nat
  state_chi :: \<open>'a set\<close>

definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> \<lparr>state_k = 0, state_chi = {}\<rparr>\<close>

locale algo_params =
  fixes threshold :: nat and f :: real
begin

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
    in if card chi < threshold
      then return_pmf (state\<lparr>state_chi := chi\<rparr>)
      else do {
        keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow> prod_pmf chi \<lblot>bernoulli_pmf f\<rblot>;

        let chi = Set.filter keep_in_chi chi;

        return_pmf (\<lparr>state_k = k + 1, state_chi = chi\<rparr>) }\<close>

definition step_3 :: "'a state \<Rightarrow> 'a state spmf" where
  "step_3 \<equiv> \<lambda> state.
    if card (state_chi state) < threshold
    then return_spmf state 
    else fail_spmf"

definition step :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step \<equiv> \<lambda> x state. spmf_of_pmf (step_1 x state \<bind> step_2) \<bind> step_3\<close>

abbreviation \<open>run_steps \<equiv> foldM_spmf step\<close>

end

locale algo_params_assms = algo_params +
  assumes
    threshold : \<open>threshold > 0\<close> and
    f : \<open>0 < f\<close> \<open>f < 1\<close>

end