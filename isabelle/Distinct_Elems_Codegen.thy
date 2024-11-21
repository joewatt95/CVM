theory Distinct_Elems_Codegen

imports
  Executable_Randomized_Algorithms.Basic_Randomized_Algorithms
  CVM.Distinct_Elems_Algo

begin

context
  fixes threshold :: nat
begin

definition "fail_ra \<equiv> lub_ra {}"

lemma
  "spmf_of_ra fail_ra = fail_spmf"
  by (simp add: fail_ra_def fail_spmf_def spmf_of_ra_lub_ra_empty) 

(*
Codegen from sets? What concrete data types and performance characteristics
are used here? RBTree? HAMT?

Can we do monadic folds over sets?

Can generalise over input sequence type, like to have a lazy streams as input?
Because if we can fit everything in memory, we might as well just use the
exact, deterministic algorithm instead.
*)

definition step_ra :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state random_alg\<close> where
  \<open>step_ra x state \<equiv> do {
    let k = state_k state;
    let chi = state_chi state;

    insert_x_into_chi \<leftarrow> bernoulli_ra <| 1 / 2 ^ k;

    let chi = (chi |>
      if insert_x_into_chi
      then insert x
      else Set.remove x);

    if card chi < threshold
    then return_ra (state\<lparr>state_chi := chi\<rparr>)
    else do {
      keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
        undefined;

      let chi = Set.filter keep_in_chi chi;

      if card chi < threshold
      then return_ra \<lparr>state_k = k + 1, state_chi = chi\<rparr>
      else fail_ra }}\<close>

value "insert (1 :: nat) {}"

term fold1

term folding

end

end