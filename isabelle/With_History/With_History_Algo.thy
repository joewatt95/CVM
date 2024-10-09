theory With_History_Algo

imports
  "HOL-Matrix_LP.Matrix"
  CVM.Basic_Algo
  CVM.Utils_List
  CVM.Utils_Option

begin

record (overloaded) 'a state_with_history = \<open>'a state\<close> +
  state_seen_elems :: \<open>'a list\<close>
  state_seen_coin_flips :: \<open>bool option matrix\<close>

definition initial_state :: \<open>'a state_with_history\<close> where
  \<open>initial_state =
    state.extend basic_algo.initial_state
      \<lparr>state_seen_elems = [], state_seen_coin_flips = 0\<rparr>\<close>

locale with_history = basic_algo
begin

definition flip_coins_and_record where
  \<open>flip_coins_and_record num_flips p state \<equiv> do {
    \<comment> \<open>Generate a sequence of `num_flips` coin flips via `Pi_pmf`.\<close>
    new_coin_flips :: nat \<Rightarrow> bool \<leftarrow>
      Pi_pmf {0 ..< num_flips} False \<lblot>bernoulli_pmf p\<rblot>;

    \<comment> \<open>`seen_coin_flips :: nat \<Rightarrow> nat \<Rightarrow> bool option` represents the
      matrix of previously seen coin flips.\<close>
    let seen_coin_flips = Rep_matrix (state_seen_coin_flips state);
    let k = state_k state;

    \<comment> \<open>Append the sequence of new coin flips to the kth row of `seen_coin_flips`.
    Technically, this is done by finding the smallest column of the kth row that
    is None, and then mapping the subsequent `num_flips` columns into
    `new_coin_flips`.\<close>
    let start_index = (LEAST index. seen_coin_flips k index = None);
    let seen_coin_flips_k =
      override_on
        (seen_coin_flips k)
        (\<lambda> index. Some (new_coin_flips <| index - start_index))
        {start_index ..< start_index + num_flips};
    \<comment> \<open>Update the kth row of `seen_coin_flips` and convert it back to a matrix.\<close>
    let seen_coin_flips =
      Abs_matrix (seen_coin_flips(k := seen_coin_flips_k));

    \<comment> \<open>Return the sequence of new coin flips along with the new state, with its
    history of coin flips updated.\<close>
    return_pmf
      (new_coin_flips, state\<lparr>state_seen_coin_flips := seen_coin_flips\<rparr>) }\<close>

definition lookup_coin_flip where
  \<open>lookup_coin_flip k index state \<equiv> (
    state
      |> state_seen_coin_flips
      |> Rep_matrix |> uncurry
      |> ((|>) (k, index)))\<close>

definition step_with_history ::
  \<open>'a \<Rightarrow> ('a, 'b) state_with_history_scheme \<Rightarrow> ('a, 'b) state_with_history_scheme spmf\<close> where
  \<open>step_with_history x state \<equiv> do {
    let seen_elems = x # state_seen_elems state;
    let state = state\<lparr>state_seen_elems := seen_elems\<rparr>;

    let k = state_k state;
    let chi = state_chi state;

    (coin_flips, state) \<leftarrow> flip_coins_and_record 1 (1 / 2 ^ k) state;

    let chi = (chi |>
      if coin_flips 0
      then insert x
      else Set.remove x);

    if card chi < threshold
    then return_spmf (state\<lparr>state_chi := chi\<rparr>)
    else do {
      (coin_flips, state) \<leftarrow>
        flip_coins_and_record (length seen_elems) (1 / 2) state; 

      let chi = {x \<in> chi. \<exists> index.
        least_index seen_elems x = Some index
          \<and> coin_flips index};

      return_spmf (state\<lparr>state_k := k + 1, state_chi := chi\<rparr>) }}\<close>

end

end