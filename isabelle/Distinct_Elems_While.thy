theory Distinct_Elems_While

imports
  Probabilistic_While.While_SPMF
  CVM.Distinct_Elems_Algo

begin

context with_threshold
begin

definition step_while :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step_while x state \<equiv> do {
    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ (state_k state);

    let chi = (state
      |> state_chi
      |> if insert_x_into_chi
        then insert x
        else Set.remove x);

    state\<lparr>state_chi := chi\<rparr>
      |> loop_spmf.while (\<lambda> state.
        card (state_chi state) \<ge> threshold) (\<lambda> state. do {
          keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
            prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

          let chi = Set.filter keep_in_chi (state_chi state);
          let k = Suc (state_k state);

          return_spmf \<lparr>state_k = k, state_chi = chi\<rparr>}) }\<close>

definition estimate_distinct_while :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_distinct_while \<equiv> run_steps_then_estimate_spmf step_while\<close>

end

end