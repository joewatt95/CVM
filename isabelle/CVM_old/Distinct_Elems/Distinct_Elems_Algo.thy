section \<open> TODO \<close>
theory Distinct_Elems_Algo

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Utils_List
  Utils_PMF_Basic
  Utils_SPMF_FoldM

begin

record 'a state =
  state_k :: nat
  state_chi :: \<open>'a set\<close>

definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> \<lparr>state_k = 0, state_chi = {}\<rparr>\<close>

definition compute_estimate :: \<open>('a, 'b) state_scheme \<Rightarrow> nat\<close> where
  \<open>compute_estimate state \<equiv> card (state_chi state) * 2 ^ (state_k state)\<close>

context
  fixes
    foldM :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> ('e, 'h) state_scheme \<Rightarrow> 'f\<close> and
    map :: \<open>(('e, 'h) state_scheme \<Rightarrow> nat) \<Rightarrow> 'f \<Rightarrow> 'g\<close> and
    step :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c\<close>
begin

definition run_steps_then_estimate ::
  \<open>('e, 'h) state_scheme \<Rightarrow> 'd \<Rightarrow> 'g\<close> where
  \<open>run_steps_then_estimate \<equiv> \<lambda> initial_state.
    flip (foldM step) initial_state >>> map compute_estimate\<close>

end

abbreviation
  \<open>run_steps_then_estimate_pmf \<equiv> run_steps_then_estimate foldM_pmf map_pmf\<close>

locale with_threshold =
  fixes threshold :: nat
begin

text
  \<open>The algorithm is defined in the SPMF monad (with None representing failure)\<close>

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
        prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi chi;
      let k = k + 1;

      if card chi < threshold
      then return_spmf \<lparr>state_k = k, state_chi = chi\<rparr>
      else fail_spmf }}\<close>

abbreviation
  \<open>run_steps_then_estimate_spmf \<equiv>
    run_steps_then_estimate foldM_spmf map_spmf\<close>

definition estimate_distinct :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_distinct \<equiv> run_steps_then_estimate_spmf step initial_state\<close>

end

locale with_threshold_pos = with_threshold +
  assumes threshold_pos : \<open>threshold > 0\<close>

end