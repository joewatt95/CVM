theory Algo_Main

imports
  "HOL-Library.Pattern_Aliases"
  "HOL-Probability.Product_PMF"
  (* Frequency_Moments.Frequency_Moments *)
  CVM.Utils_Function
  CVM.Utils_PMF
  CVM.Algo_Params

begin

context params begin

context includes pattern_aliases begin

definition initial_state :: state where
  [simp] : "initial_state \<equiv> \<lparr>state_p = 1, state_chi = {}\<rparr>"

(* definition initial_trace :: trace where
  [simp] : "initial_trace \<equiv> [initial_state]" *)

fun step :: "nat \<Rightarrow> state \<Rightarrow> state option pmf" where
  "step x (\<lparr>state_p = p, state_chi = chi\<rparr> =: state) = do {
    remove_x_from_chi \<leftarrow> bernoulli_pmf p;
    let chi = (chi
      |> flip (-) {x}
      |> if remove_x_from_chi then id else insert x);

    if card chi < threshold
    then return_pmf <| Some <| state\<lparr>state_chi := chi\<rparr>
    else do {

    keep_in_chi :: nat \<Rightarrow> bool \<leftarrow>
      Pi_pmf chi False <| \<lambda> _. bernoulli_pmf <| (1 :: real) / 2;

    let chi = Set.filter keep_in_chi chi;

    return_pmf <|
      if card chi = threshold
      then None
      else Some \<lparr>state_p = p / 2, state_chi = chi\<rparr> }}"

abbreviation steps_to ("\<turnstile> _ \<rightarrow> [ _ ] \<rightarrow> _" [999, 999, 999]) where
  "steps_to state x state' \<equiv> step x state = return_pmf (Some state')"

abbreviation doesnt_step_to ("⊬ _ \<rightarrow> [ _ ] \<rightarrow> " [999, 999]) where
  "doesnt_step_to state x \<equiv> step x state = return_pmf None"

fun result :: "state \<Rightarrow> nat" where
  "result \<lparr>state_p = p, state_chi = chi\<rparr> =
    nat \<lfloor>(card chi :: real) / p\<rfloor>"

definition estimate_size :: "nat list \<Rightarrow> nat option pmf" where
  "estimate_size xs \<equiv>
    (initial_state
      |> Some
      |> foldM_option_pmf step xs
      |> map_pmf (map_option result))"

end

end

end