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

end

end