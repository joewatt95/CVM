theory Basic_Props_Without_Failure

imports
  CVM.Basic_Algo

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

lemma step_lossless :
  \<open>lossless_spmf <| step False x state\<close>

  unfolding step_def by (simp add: Let_def)

lemma estimate_distinct_lossless :
  \<open>lossless_spmf <| estimate_distinct False xs\<close>

  by (simp add: estimate_distinct_def foldM_spmf_lossless_of_always_lossless run_steps_def step_lossless)

lemma estimate_distinct_pmf :
  obtains estimate_distinct_pmf ::
    \<open>'a list \<Rightarrow> 'a final_state pmf\<close> where 
    \<open>spmf_of_pmf <<< estimate_distinct_pmf = estimate_distinct False\<close>
proof -
  let ?R = \<open>\<lambda> p xs. spmf_of_pmf p = estimate_distinct False xs\<close>

  have \<open>\<forall> xs. \<exists> p. ?R p xs\<close>
    by (metis estimate_distinct_lossless lossless_spmf_conv_spmf_of_pmf)

  (* Note: metis struggles with the higher-order \<exists> involved with Choice. *)
  then have \<open>\<exists> choice_fn. \<forall> xs. ?R (choice_fn xs) xs\<close> by (fast intro: choice)

  then show ?thesis using that by auto
qed

end

end