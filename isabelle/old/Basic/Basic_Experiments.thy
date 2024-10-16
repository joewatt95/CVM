theory Basic_Experiments

imports
  CVM.Basic_Algo

begin

context basic_algo
begin

definition step' ::
  \<open>'a \<Rightarrow> ('a, 'b) state_scheme \<Rightarrow> ('a, 'b) state_scheme pmf\<close> where
  \<open>step' x state \<equiv> do {
    let k = state_k state;
    let chi = state_chi state;

    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ k;

    let chi = (chi |>
      if insert_x_into_chi
      then insert x
      else Set.remove x);

    if card chi < threshold
    then return_pmf (state\<lparr>state_chi := chi\<rparr>)
    else do {
      keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
        Pi_pmf chi undefined \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi chi;

      return_pmf (state\<lparr>state_k := k + 1, state_chi := chi\<rparr>) }}\<close>

lemma
  \<open>\<P>(state' in step' x state. state_k state' = k \<longrightarrow> x \<in> state_chi state')
    = 1 / 2 ^ k\<close>

  apply (cases state)

  unfolding
    step'_def Let_def
    state.simps state.defs
    Set.filter_def Set.remove_def
    map_bind_pmf bind_map_pmf
    map_pmf_def[symmetric] map_pmf_comp

  find_theorems "measure_pmf" "bind_pmf"

  apply (simp add:
    measure_pmf_bind
  )

  sorry


end

end