theory Basic_Algo

imports
  "HOL-Library.Pattern_Aliases"
  "HOL-Probability.Product_PMF"
  "HOL-Probability.SPMF"
  CVM.Utils_Function
  CVM.Utils_PMF
  CVM.Utils_SPMF_Common

begin

record 'a state =
  state_p :: real
  state_chi :: \<open>'a set\<close>

locale basic_algo =
  fixes threshold :: real
begin

context includes pattern_aliases
begin

definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> \<lparr>state_p = 1, state_chi = {}\<rparr>\<close>

(* definition initial_trace :: \<open>'a trace\<close> where
  [simp] : \<open>initial_trace \<equiv> [Some initial_state]\<close> *)

definition step :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  (* \<open>step x (\<lparr>state_p = p, state_chi = chi\<rparr> =: state) = do { *)
  \<open>step x state \<equiv> do {
    let p = state_p state;
    let chi = state_chi state;
    remove_x_from_chi \<leftarrow> spmf_of_pmf <| bernoulli_pmf p;
    let chi = (chi |> if remove_x_from_chi then Set.remove x else insert x);

    if card chi \<ge> threshold
    then do {
      keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
        spmf_of_pmf <|
          Pi_pmf chi undefined \<lblot>bernoulli_pmf ((1 :: real) / 2)\<rblot>;

      let chi = (chi |> Set.filter keep_in_chi);

      if card chi \<ge> threshold
      then fail_spmf
      else return_spmf \<lparr>state_p = p / 2, state_chi = chi\<rparr> }
    else return_spmf (state\<lparr>state_chi := chi\<rparr>) }\<close>

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
  \<open>result \<lparr>state_p = p, state_chi = chi\<rparr> =
    nat \<lfloor>(card chi :: real) / p\<rfloor>\<close>

definition estimate_size :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_size \<equiv> run_steps initial_state >>> map_spmf result\<close>

end

end

end