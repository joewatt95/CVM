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

context
  fixes fail_if_threshold_exceeded :: bool
  assumes
    threshold_pos : \<open>threshold > 0\<close> and
    dont_fail_if_threshold_exceeded : \<open>\<not> fail_if_threshold_exceeded\<close>
begin

lemma step_lossless :
  fixes
    x :: 'a and
    state :: \<open>'a state\<close>
  shows \<open>lossless_spmf <| step fail_if_threshold_exceeded x state\<close>

  unfolding step_def
  by (simp add: dont_fail_if_threshold_exceeded Let_def)

lemma run_steps_lossless :
  fixes
    xs :: \<open>'a list\<close> and
    state :: \<open>'a state\<close>
  shows \<open>lossless_spmf <| run_steps fail_if_threshold_exceeded state xs\<close>

  by (metis run_steps_def foldM_spmf_lossless_of_always_lossless step_lossless)

lemma estimate_distinct_lossless :
  fixes xs :: \<open>'a list\<close>
  shows \<open>lossless_spmf <| estimate_distinct fail_if_threshold_exceeded xs\<close>

  by (simp add: estimate_distinct_def run_steps_lossless)

end

end

end