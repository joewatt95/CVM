theory Basic_Props

imports
  Basic_Props_With_Failure
  Basic_Props_Without_Failure

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
  fixes
    fail :: bool and
    dont_fail :: bool
  (* assumes
    fail : \<open>fail\<close> and
    dont_fail : \<open>\<not> dont_fail\<close> *)
begin

abbreviation step_with_failure where
  \<open>step_with_failure \<equiv> step fail\<close>

abbreviation step_without_failure where
  \<open>step_without_failure \<equiv> step dont_fail\<close>

(* definition rel where
  \<open>rel state state' \<equiv> 0\<close> *)

(* lemma test :
  \<open>rel_spmf <| \<lambda>\<close> *)

end

end

end