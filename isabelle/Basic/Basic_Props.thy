theory Basic_Props

imports
  CVM.Basic_Props_With_Failure
  CVM.Basic_Props_Without_Failure
  CVM.Utils_SPMF_Rel

begin

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

(*
The idea here is as follows:
1. We first show that each iteration of the loop with failure (ie `step True`)
   agrees with the corresponding iteration that doesn't fail (ie `step False` )
   wherever the former doesn't fail.

2. We then extend this equivalence to the whole algorithm, across all the loop
   iterations, ie for `estimate_distinct True` and `estimate_distinct False`.

3. Next, we argue that because of the above step, if we fix a predicate `P`,
   Prob of a successful, non-failure output of `estimate_distinct True` satisfying
   O \<le> that of `estimate_distinct False`.

   Note here that in particular, we can instantiate `P` with a predicate that
   says that the output is out of \<epsilon> range of the true value we're estimating.

4. We then bound:
    Prob of `estimate_distinct True` failing or outputting a value that satisfies P
    \<le> Prob of `estimate_distinct True` failing + Prob of `estimate_distinct True` outputting a value that satisfies P
    \<le> length xs * 2 powr threshold + Prob of `estimate_distinct False` outputting a value that satisfies P

These (in particular steps 1 - 3) are formalised with the help of `ord_spmf`
and `rel_pmf`.
For more details, see Utils/SPMF/Utils_SPMF_Rel.thy 
*)

lemma step_ord_spmf_eq :
  \<open>ord_spmf (=) (step True x state) <| step False x state\<close>

  by (auto
      intro!: ord_spmf_bind_reflI
      simp del: bind_spmf_of_pmf
      simp add: step_def fail_spmf_def bind_spmf_of_pmf[symmetric] Let_def)

lemma estimate_distinct_ord_spmf_eq :
  \<open>ord_spmf (=) (estimate_distinct True xs) <| estimate_distinct False xs\<close>

  by (auto
      intro: foldM_spmf_ord_spmf_eq_of_ord_spmf_eq step_ord_spmf_eq ord_spmf_mono
      simp add: estimate_distinct_def run_steps_def ord_spmf_map_spmf)

context
  fixes
    P :: \<open>'a final_state \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close>
begin

private abbreviation prob_P :: \<open>bool \<Rightarrow> real\<close> where
  \<open>prob_P fail \<equiv>
    \<P>(state' in measure_spmf <| estimate_distinct fail xs. P state')\<close>

lemma prob_estimate_distinct_le :
  \<open>prob_P True \<le> prob_P False\<close>

  by (auto intro: prob_le_prob_of_ord_spmf_eq estimate_distinct_ord_spmf_eq)

lemma prob_estimate_distinct_fail_or_satisfies_le :
  assumes \<open>threshold > 0\<close>
  shows
    \<open>\<P>(result in estimate_distinct True xs. result |> fail_or_satisfies P)
      \<le> (length xs :: real) * 2 powr threshold + prob_P False\<close>

  by (smt (verit, best) Collect_cong assms prob_estimate_distinct_le prob_fail_estimate_size_le prob_fail_or_satisfies_le_prob_fail_plus_prob) 

end

end

end