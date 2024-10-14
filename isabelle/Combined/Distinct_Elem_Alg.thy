section \<open> TODO \<close>
theory Distinct_Elem_Alg

imports
  CVM.Utils_PMF
  CVM.Utils_SPMF_FoldM
begin

record 'a state =
  state_k :: nat
  state_chi :: \<open>'a set\<close>

locale with_threshold =
  fixes threshold :: nat
  assumes threshold_pos: "threshold > 0"
begin

definition step :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step x state \<equiv> do {
    let k = state_k state;
    let chi = state_chi state;

    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ k;

    let chi = (chi |>
      if insert_x_into_chi
      then insert x
      else Set.remove x);

    if card chi < threshold
    then return_spmf (state\<lparr>state_chi := chi\<rparr>)
    else do {
      keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
        Pi_pmf chi undefined \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi chi;

      if card chi < threshold
      then return_spmf <| state\<lparr>state_k := k + 1, state_chi := chi\<rparr>
      else fail_spmf
    }}\<close>

definition run_steps :: \<open>'a state \<Rightarrow> 'a list \<Rightarrow> 'a state spmf\<close> where
  \<open>run_steps \<equiv> flip (foldM_spmf step)\<close>

definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> \<lparr>state_k = 0, state_chi = {}\<rparr>\<close>

text \<open> The algorithm is defined in the SPMF monad (with None representing failure) \<close>
definition estimate_distinct :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_distinct \<equiv>
    run_steps initial_state >>>
    map_spmf (\<lambda>state. card (state_chi state) * 2 ^ (state_k state))\<close>

end

end