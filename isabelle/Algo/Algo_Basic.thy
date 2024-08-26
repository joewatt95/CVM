theory Algo_Basic

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

definition initial_state :: "'a state" where
  [simp] : "initial_state \<equiv> \<lparr>state_p = 1, state_chi = {}\<rparr>"

definition initial_trace :: "'a trace" where
  [simp] : "initial_trace \<equiv> [initial_state]"

fun step :: "'a \<Rightarrow> 'a trace \<Rightarrow> 'a trace option pmf" where "
  step x ((\<lparr>state_p = p, state_chi = chi\<rparr> =: state) # states) = do {
    remove_x_from_chi \<leftarrow> bernoulli_pmf p;
    let chi = (chi |> if remove_x_from_chi then Set.remove x else insert x);

    if card chi \<ge> threshold
    then do {
      keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
        Pi_pmf chi False <| \<lambda> _. bernoulli_pmf ((1 :: real) / 2);

      let chi = (chi |> Set.filter keep_in_chi);

      return_pmf <|
        if card chi \<ge> threshold
        then None
        else Some (\<lparr>state_p = p / 2, state_chi = chi\<rparr> # states) }
    else return_pmf (Some <| state\<lparr>state_chi := chi\<rparr> # states) }" | "
    
  step _ _ = return_pmf None"

definition run_steps :: "
  'a list \<Rightarrow> 'a state list \<Rightarrow> 'a state list option pmf" where
  [simp] : "run_steps \<equiv> foldM_option_pmf step"

fun result :: "'a state \<Rightarrow> nat" where "
  result \<lparr>state_p = p, state_chi = chi\<rparr> =
    nat \<lfloor>(card chi :: real) / p\<rfloor>"

fun estimate_size :: "'a list \<Rightarrow> nat option pmf" where "
  estimate_size xs = (
    initial_trace
      |> run_steps xs
      |> map_option_pmf (result \<circ> hd))"

end

end

end