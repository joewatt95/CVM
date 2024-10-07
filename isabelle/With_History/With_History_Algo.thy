theory With_History_Algo

imports
  CVM.Basic_Algo
  CVM.Utils_List

begin

record 'a state_with_history = \<open>'a state\<close> +
  state_seen_elems :: \<open>'a list\<close>
  state_seen_coin_flips :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool option\<close>

definition initial_state :: \<open>'a state_with_history\<close> where
  \<open>initial_state =
    state.extend basic_algo.initial_state
      \<lparr>state_seen_elems = [], state_seen_coin_flips = curry \<lblot>None\<rblot>\<rparr>\<close>

locale with_history = basic_algo
begin

(* definition record_coin_flip where
  \<open>record_coin_flip k index b state \<equiv> (
    if \<not> track_coin_flip_history opts
    then state
    else
      let
        update_history = \<lambda> coin_flip_history.
          coin_flip_history
            \<lparr>history := (history coin_flip_history)((k, index) := Some b)\<rparr>
      in state
        \<lparr>state_coin_flip_history :=
          state |> state_coin_flip_history |> map_option update_history\<rparr>)\<close> *)

definition flip_coins_and_record where
  \<open>flip_coins_and_record start_index num_bits p state \<equiv> do {
    new_coin_flips :: nat \<Rightarrow> bool \<leftarrow>
      Pi_pmf {0 ..< num_bits} False \<lblot>bernoulli_pmf p\<rblot>;

    let seen_coin_flips = state_seen_coin_flips state;
    let k = state_k state;

    let seen_coin_flips_k =
      override_on
        (seen_coin_flips k)
        (\<lambda> index. Some (new_coin_flips <| index - start_index))
        {start_index ..};

    let seen_coin_flips = seen_coin_flips(k := seen_coin_flips_k);

    return_pmf
      (new_coin_flips, state\<lparr>state_seen_coin_flips := seen_coin_flips\<rparr>) }\<close>

definition lookup_coin_flip where
  \<open>lookup_coin_flip k index state \<equiv> (
    state
      |> state_seen_coin_flips
      |> uncurry
      |> ((|>) (k, index)))\<close>

definition step_with_history ::
  \<open>'a \<Rightarrow> 'a state_with_history \<Rightarrow> 'a state_with_history pmf\<close> where
  \<open>step_with_history x state \<equiv> do {
    let seen_elems = x # state_seen_elems state;
    let state = state\<lparr>state_seen_elems := seen_elems\<rparr>;

    let k = state_k state;
    let chi = state_chi state;

    (coin_flips, state) \<leftarrow> flip_coins_and_record 0 1 (1 / 2 ^ k) state;

    let chi = (chi |>
      if coin_flips 0
      then insert x
      else Set.remove x);

    if card chi < threshold
    then return_pmf (state\<lparr>state_chi := chi\<rparr>)
    else do {
      (coin_flips, state) \<leftarrow>
        flip_coins_and_record 1 (length seen_elems) (1 / 2) state; 

      let chi = {x \<in> chi. \<exists> index.
        greatest_index seen_elems x = Some index
          \<and> coin_flips index};

      return_pmf (state\<lparr>state_k := k + 1, state_chi := chi\<rparr>) }}\<close>

end

end