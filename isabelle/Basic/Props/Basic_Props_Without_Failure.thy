theory Basic_Props_Without_Failure

imports
  CVM.Basic_Algo

begin

text \<open> Directly relate step to step_pmf version using the relator \<close>
context basic_algo
begin

definition step_pmf :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_pmf x state \<equiv> do {
    let k = state_k state;
    let chi = state_chi state;

    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ k;

    let chi = (chi |>
      if insert_x_into_chi
      then insert x
      else Set.remove x);

    if card chi < threshold
    then return_pmf (state\<lparr>state_chi := chi\<rparr>)
    else do {
      keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
        Pi_pmf chi undefined \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi chi;

      return_pmf (state\<lparr>state_k := k + 1, state_chi := chi\<rparr>)
 } }\<close>

lemma rel_pmf_step_aux:
  shows "rel_pmf (\<lambda>s p. s = Some p) (step No_fail x state) (step_pmf x state)"
  unfolding step_def step_pmf_def Let_def
  apply (subst rel_pmf_bindI[of "(=)"])
  apply (auto simp add: pmf.rel_eq)
  apply (smt (verit, del_insts) pmf.rel_eq rel_pmf_bindI rel_return_pmf)
  by (smt (verit, del_insts) pmf.rel_eq rel_pmf_bindI rel_return_pmf)

lemma rel_pmf_step:
  shows "step No_fail x state = map_pmf Some (step_pmf x state)"
  apply (subst pmf.rel_eq[symmetric])
  by (auto simp add: pmf.rel_map rel_pmf_step_aux)

end

(*
Here we show that the execution of
`estimate_distinct False :: 'a list \<Rightarrow> 'a final_state spmf` never fails so that
the result can always be lifted out of the spmf monad into pmf.
More precisely, we obtain a function
`estimate_distinct_pmf :: 'a list \<Rightarrow> 'a final_state pmf` such that
`spmf_of_pmf <<< f = estimate_distinct False`.

To do this:
1. We first show that each step (ie `step False`) of the loop is lossless, ie
   `lossless_spmf <| step False x state`.

2. We use the above to prove the same for `estimate_distinct False`, ie
   `lossless_spmf <| estimate_distinct False xs`.

   With this, if we fix any `xs`, we can lift the result of
   `estimate_distinct False xs` out of `spmf` and into `pmf`.

3. We then appeal to Choice (and an indefinite description operator) to define
   `estimate_distinct_pmf` as a choice function mapping each input `xs` to its
   corresponding (lifted) result in the `pmf` monad.
*)

sledgehammer_params [
  (* verbose *)
  minimize = true,
  preplay_timeout = 15,
  timeout = 60,
  max_facts = smart,
  provers = "
    cvc4 z3 verit
    e vampire spass
  "
]

context basic_algo
begin

lemma step_lossless :
  \<open>lossless_spmf <| step No_fail x state\<close>

  unfolding step_def by (simp add: Let_def)

lemma estimate_distinct_lossless :
  \<open>lossless_spmf <| estimate_distinct No_fail xs\<close>

  by (simp add: estimate_distinct_def foldM_spmf_lossless_of_always_lossless run_steps_def step_lossless)

abbreviation (input) P where
  \<open>P f \<equiv> spmf_of_pmf <<< f = estimate_distinct No_fail\<close>

definition estimate_distinct_pmf :: \<open>'a list \<Rightarrow> 'a state_with_estimate pmf\<close> where
  \<open>estimate_distinct_pmf \<equiv> \<some> f. P f\<close>

(*
This Lemma appeals to Choice (and an indefinite description operator) to define
`estimate_distinct_pmf` as a choice function mapping each input `xs` to its
 corresponding result in the `pmf` monad, lifted from `spmf`.

Note:
- While sledgehammer can work out the required lemmas, the reconstruction methods
  like metis and smt struggled heavily with the 2nd order \<exists> involved when
  invoking Choice to invert \<forall> \<exists> to \<exists> \<forall>.
  auto and related tactics like fastforce all struggled with that as well.

- Our appeal to Choice and its non-constructiveness can get in the way of future
  proofs, in that the lack of an explicit closed form expression witnessing
  the existential means that we cannot perform simplification (ie symbolic
  execution) directly on it.
  This must all be done indirectly via the original spmf version.
*)
lemma spmf_of_pmf_estimate_distinct_pmf_eq :
  \<open>P estimate_distinct_pmf\<close>
proof -
  let ?R = \<open>\<lambda> p xs. spmf_of_pmf p = estimate_distinct No_fail xs\<close>

  have \<open>\<forall> xs. \<exists> p. ?R p xs\<close>
    by (metis estimate_distinct_lossless lossless_spmf_conv_spmf_of_pmf)

  then have \<open>\<exists> choice_fn. \<forall> xs. ?R (choice_fn xs) xs\<close> by (rule choice)

  then have \<open>\<exists> choice_fn. P choice_fn\<close> by blast

  then show ?thesis unfolding estimate_distinct_pmf_def by (rule someI_ex)
qed

(* lemma prob_estimate_distinct_pmf_eq :
  fixes P
  shows
    \<open>\<P>(result in estimate_distinct_pmf xs. P result)
      = \<P>(result in measure_spmf <| estimate_distinct False xs. P result)\<close>

  by (metis (no_types, lifting) Collect_cong spmf_of_pmf_estimate_distinct_pmf_eq measure_spmf_spmf_of_pmf)  *)

end

end