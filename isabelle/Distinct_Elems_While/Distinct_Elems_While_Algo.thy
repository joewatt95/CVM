theory Distinct_Elems_While_Algo

imports
  CVM.Distinct_Elems_Algo

begin

context with_threshold
begin

definition cond :: \<open>('a, 'b) state_scheme \<Rightarrow> bool\<close> where
  \<open>cond \<equiv> \<lambda> state. card (state_chi state) \<ge> threshold\<close>

definition body :: \<open>('a, 'b) state_scheme \<Rightarrow> ('a, 'b) state_scheme pmf\<close> where
 \<open>body \<equiv> \<lambda> state. do {
  let chi = state_chi state;

  keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
    prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

  let chi = Set.filter keep_in_chi chi;
  let k = state_k state + 1;

  return_pmf (state\<lparr>state_k := k, state_chi := chi\<rparr>)}\<close>

abbreviation \<open>body_spmf \<equiv> spmf_of_pmf <<< body\<close>

definition step_while ::
  \<open>'a \<Rightarrow> ('a, 'b) state_scheme \<Rightarrow> ('a, 'b) state_scheme spmf\<close> where
  \<open>step_while x state \<equiv> do {
    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ (state_k state);

    let chi = (state
      |> state_chi
      |> if insert_x_into_chi
        then insert x
        else Set.remove x);

    loop_spmf.while cond body_spmf (state\<lparr>state_chi := chi\<rparr>) }\<close>

definition estimate_distinct_while :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_distinct_while \<equiv>
    run_steps_then_estimate_spmf step_while initial_state\<close>

end

end