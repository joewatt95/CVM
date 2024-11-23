theory Distinct_Elems_While

imports
  Probabilistic_While.While_SPMF
  CVM.Distinct_Elems_Algo
  CVM.Algo_Transforms_No_Fail

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
          let k = state_k state + 1;

          return_spmf \<lparr>state_k = k, state_chi = chi\<rparr>}) }\<close>

definition estimate_distinct_while :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_distinct_while \<equiv> run_steps_then_estimate_spmf step_while\<close>

(* Probabilistic while loops are defined as the limit (ie sup) of the usual
(increasing) transfinite sequence over the CCPO structure on spmf.
See https://pcousot.github.io/publications/Cousot-LOPSTR-2019.pdf

Thus, to prove that a property holds of a loop, one essentially shows that the
property is a loop invariant by performing transfinite induction over the
sequence, aka Scott induction.
The 3 cases of the `loop_spmf.while_fixp_induct` rule correspond to each case
of the transfinite sequence, namely:
`adm` aka CCPO admissibility, handles limit ordinals.
`bottom` handles the base case, with `\<bottom> = return_pmf None`
`step` handles successor ordinals.

Note that in general, endofunctors over spmf need not be Scott continuous
(see pg 560 of https://ethz.ch/content/dam/ethz/special-interest/infk/inst-infsec/information-security-group-dam/research/publications/pub2020/Basin2020_Article_CryptHOLGame-BasedProofsInHigh.pdf )
so that fixpoints may only be found beyond \<omega>, which means that one may not be
able to consider only \<omega>-chains for the `adm` step. *)
thm loop_spmf.while_fixp_induct[
  unfolded ccpo.admissible_def Ball_def fun_ord_def fun_lub_def]

lemma
  \<open>do {
    state
      |> loop_spmf.while (\<lambda> state.
        card (state_chi state) \<ge> threshold) (\<lambda> state. do {
          keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
            prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

          let chi = Set.filter keep_in_chi (state_chi state);
          let k = state_k state + 1;

          return_spmf \<lparr>state_k = k, state_chi = chi\<rparr>}) }
  = (
    if card (state_chi state) < threshold
    then return_spmf state
    else do {
      keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
        prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let k = state_k state;
      let chi = Set.filter keep_in_chi chi;

      if card chi < threshold
      then return_spmf \<lparr>state_k = k + 1, state_chi = chi\<rparr>
      else fail_spmf
    } )\<close>
  sorry

end

end