theory Basic_Props_Without_Failure

imports
  CVM.Basic_Algo

begin

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
  \<open>lossless_spmf <| step False x state\<close>

  unfolding step_def by (simp add: Let_def)

lemma estimate_distinct_lossless :
  \<open>lossless_spmf <| estimate_distinct False xs\<close>

  by (simp add: estimate_distinct_def foldM_spmf_lossless_of_always_lossless run_steps_def step_lossless)

abbreviation (input) P where
  \<open>P f \<equiv> spmf_of_pmf <<< f = estimate_distinct False\<close>

definition estimate_distinct_pmf :: \<open>'a list \<Rightarrow> 'a final_state pmf\<close> where
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
  let ?R = \<open>\<lambda> p xs. spmf_of_pmf p = estimate_distinct False xs\<close>

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