theory Basic_Algo

imports
  "HOL-Probability.Product_PMF"
  "Finite-Map-Extras.Finite_Map_Extras"
  CVM.Utils_PMF
  CVM.Utils_SPMF_FoldM

begin

record 'a state =
  state_k :: nat
  state_chi :: \<open>'a set\<close>

  state_flipped_coins :: \<open>(nat \<times> nat, bool) fmap\<close>

record 'a final_state = \<open>'a state\<close> +
  state_estimated_size :: nat

locale basic_algo =
  fixes threshold :: real
begin

datatype Fail_if_threshold_exceeded
  = Fail
  | No_fail

abbreviation (input) bool_of_fail :: \<open>Fail_if_threshold_exceeded \<Rightarrow> bool\<close> where
  \<open>bool_of_fail \<equiv> (=) Fail\<close>

declare [[coercion bool_of_fail]]

context
  fixes fail_if_threshold_exceeded :: Fail_if_threshold_exceeded
begin

definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> \<lparr>
    state_k = 0,
    state_chi = {},
    state_flipped_coins = {$$}\<rparr>\<close>

(* definition initial_trace :: \<open>'a trace\<close> where
  \<open>initial_trace \<equiv> [Some initial_state]\<close> *)

definition step :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step x state \<equiv> do {
    let k = state_k state;
    let chi = state_chi state;

    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ k;

    let chi = (chi |>
      if insert_x_into_chi
      then insert x
      else Set.remove x);

    if card chi < threshold
    then return_spmf (state\<lparr>state_chi := chi\<rparr>)
    else do {
      keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
        Pi_pmf chi undefined \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi chi;

      if \<not> fail_if_threshold_exceeded \<or> card chi < threshold
      then return_spmf <| state\<lparr>state_k := k + 1, state_chi := chi\<rparr>
      else fail_spmf }}\<close>

find_theorems "pmf (map_pmf _ _) _"
find_theorems "measure_pmf.prob (Pi_pmf _ _ _)"

lemma
  assumes
    \<open>chi \<subseteq> set xs\<close>
  shows
    \<open>map_pmf (flip Set.filter chi) (Pi_pmf chi undefined \<lblot>bernoulli_pmf <| 1 / 2\<rblot>)
      = map_pmf (\<lambda> f. {x \<in> chi. \<exists> n. f n \<and> xs ! n = x}) (Pi_pmf {0 ..< length xs} undefined \<lblot>bernoulli_pmf <| 1 / 2\<rblot>)\<close>

  apply (intro pmf_eqI)
  apply (simp add: pmf_map)

  sorry

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

definition result :: \<open>'a state \<Rightarrow> 'a final_state\<close> where
  \<open>result state \<equiv>
    state.extend state
      \<lparr>state_estimated_size = card (state_chi state) * 2 ^ (state_k state)\<rparr>\<close>

definition estimate_distinct :: \<open>'a list \<Rightarrow> 'a final_state spmf\<close> where
  \<open>estimate_distinct \<equiv> run_steps initial_state >>> map_spmf result\<close>

end

end

end