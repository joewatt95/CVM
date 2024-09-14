theory Basic_Props_Without_Failure

imports
  CVM.Basic_Props_Common

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

locale basic_props_with_failure = basic_props_common +
  assumes dont_fail_if_threshold_exceeded : \<open>\<not> fail_if_threshold_exceeded\<close>
begin

lemma step_lossless :
  fixes
    x :: 'a and
    state :: \<open>'a state\<close>
  shows \<open>lossless_spmf <| step x state\<close>

  unfolding step_def by (simp add: dont_fail_if_threshold_exceeded Let_def)

lemma run_steps_lossless :
  fixes
    xs :: \<open>'a list\<close> and
    state :: \<open>'a state\<close>
  shows \<open>lossless_spmf <| run_steps state xs\<close>

  by (metis run_steps_def spmf_foldM.foldM_spmf_lossless_of_always_lossless step_lossless)

lemma estimate_distinct_lossless :
  fixes xs :: \<open>'a list\<close>
  shows \<open>lossless_spmf <| estimate_distinct xs\<close>

  by (simp add: estimate_distinct_def run_steps_lossless)

end