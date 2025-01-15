theory CVM_Algo

imports
  "HOL-Probability.Probability_Mass_Function"
  Helper

begin

unbundle no_vec_syntax

record 'a state =
  state_k :: nat
  state_chi :: \<open>'a set\<close>

definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> \<lparr>state_k = 0, state_chi = {}\<rparr>\<close>

locale cvm_algo =
  fixes threshold :: nat and subsample_size :: nat
begin

definition f :: real 
  where "f \<equiv> subsample_size / threshold"

definition step_1 :: \<open>'a \<Rightarrow> ('a, 'b) state_scheme \<Rightarrow> ('a, 'b) state_scheme pmf\<close> where
  \<open>step_1 \<equiv> \<lambda> x state. do {
    let k = state_k state;
    let chi = state_chi state; 

    insert_x_into_chi \<leftarrow> bernoulli_pmf <| f ^ k;

    let chi = (chi |>
      if insert_x_into_chi
      then insert x
      else Set.remove x);

    return_pmf (state\<lparr>state_chi := chi\<rparr>) }\<close>

definition subsample :: \<open>'a set \<Rightarrow> 'a set pmf\<close> where
  \<open>subsample \<equiv> \<lambda> chi. pmf_of_set {S. S \<subseteq> chi \<and> card S = subsample_size}\<close>

definition step_2 :: \<open>('a, 'b) state_scheme \<Rightarrow> ('a, 'b) state_scheme pmf\<close> where
  \<open>step_2 \<equiv> \<lambda> state. do {
    let k = state_k state;
    let chi = state_chi state;

    if card chi < threshold
    then return_pmf state
    else (chi
      |> subsample
      |> map_pmf (\<lambda> chi. state\<lparr>state_k := k + 1, state_chi := chi\<rparr>)) }\<close>

definition step :: \<open>'a \<Rightarrow> ('a, 'b) state_scheme \<Rightarrow> ('a, 'b) state_scheme pmf\<close> where
  \<open>step x st \<equiv> step_1 x st \<bind> step_2\<close>

abbreviation foldM_pmf ::
  \<open>('a \<Rightarrow> 'b \<Rightarrow> 'b pmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b pmf\<close> where
  \<open>foldM_pmf \<equiv> foldM bind_pmf return_pmf\<close>

definition run_steps ::
  \<open>'a list \<Rightarrow> 'a state pmf\<close> where
  \<open>run_steps xs \<equiv> foldM_pmf step xs initial_state\<close>

end

end