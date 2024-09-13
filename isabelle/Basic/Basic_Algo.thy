theory Basic_Algo

imports
  "HOL-Library.Pattern_Aliases"
  "HOL-Probability.Product_PMF"
  CVM.Utils_PMF
  CVM.Utils_SPMF_FoldM

begin

record 'a state =
  state_k :: nat
  state_chi :: \<open>'a set\<close>

locale basic_algo =
  fixes threshold :: real
begin

context includes pattern_aliases
begin

definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> \<lparr>state_k = 0, state_chi = {}\<rparr>\<close>

(* definition initial_trace :: \<open>'a trace\<close> where
  [simp] : \<open>initial_trace \<equiv> [Some initial_state]\<close> *)

definition step :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  (* \<open>step x (\<lparr>state_p = p, state_chi = chi\<rparr> =: state) = do { *)
  \<open>step x state \<equiv> do {
    let k = state_k state;
    let chi = state_chi state;

    remove_x_from_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ k;

    let chi = (chi |>
      if remove_x_from_chi
      then Set.remove x
      else insert x);

    if card chi < threshold
    then return_spmf (state\<lparr>state_chi := chi\<rparr>)
    else do {
      keep_in_chi \<leftarrow> Pi_pmf chi undefined \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi chi;

      if card chi < threshold
      then return_spmf \<lparr>state_k = k + 1, state_chi = chi\<rparr>
      else fail_spmf } }\<close>

definition run_steps :: \<open>'a state \<Rightarrow> 'a list \<Rightarrow> 'a state spmf\<close> where
  \<open>run_steps \<equiv> flip (foldM_spmf step)\<close>

(* fun step_with_trace :: \<open>'a \<Rightarrow> 'a trace \<Rightarrow> 'a trace pmf\<close> where
  \<open>step_with_trace x (Some state # _ =: states) = do {
    state \<leftarrow> step x state;
    return_pmf <| state # states }\<close> |
  \<open>step_with_trace _ states = return_pmf states\<close> *)

(* fun run_steps_with_trace :: \<open>'a list \<Rightarrow> 'a ok_state \<Rightarrow> 'a trace pmf\<close> where
  \<open>run_steps_with_trace xs state =
    foldM_pmf step_with_trace xs [Some state]\<close>

fun run_steps :: \<open>'a list \<Rightarrow> 'a ok_state \<Rightarrow> 'a state pmf\<close> where
  \<open>run_steps x = map_pmf hd \<circ> run_steps_with_trace x\<close> *)

fun result :: \<open>'a state \<Rightarrow> nat\<close> where
  \<open>result \<lparr>state_k = k, state_chi = chi\<rparr> = card chi * 2 ^ k\<close>

definition estimate_size :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_size \<equiv> run_steps initial_state >>> map_spmf result\<close>

end

end

end