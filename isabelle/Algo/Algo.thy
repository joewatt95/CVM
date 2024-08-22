theory Algo

imports
  HOL.Option
  "HOL-Library.Pattern_Aliases"
  "HOL-Probability.Product_PMF"
  (* Frequency_Moments.Frequency_Moments *)
  CVM.Utils
  Params

begin

context params begin
context includes pattern_aliases begin

definition initial_state where
  "initial_state \<equiv> \<lparr>state_p = 1, state_chi = {}\<rparr>"

definition initial_trace where
  "initial_trace = Some [initial_state]"

(* lemma (in params) initial_state_well_formed :
  "well_formed initial_state"
  sorry *)

fun step :: "nat \<Rightarrow> trace option \<Rightarrow> trace option pmf" where
  "step x (Some ((\<lparr>state_p = p, state_chi = chi\<rparr> =: state) # _ =: states)) = do {
    remove_x_from_chi \<leftarrow> bernoulli_pmf p;
    let chi = (chi
      |> flip (-) {x}
      |> if remove_x_from_chi then id else insert x);

    if card chi < threshold
    then return_pmf <| Some <| state\<lparr>state_chi := chi\<rparr> # states
    else do {

    keep_in_chi :: nat \<Rightarrow> bool \<leftarrow>
      Pi_pmf chi False <| \<lambda> _. bernoulli_pmf <| (1 :: real) / 2;

    let chi = Set.filter keep_in_chi chi;

    return_pmf <|
      if card chi = threshold
      then None
      else
        let state = \<lparr>state_p = p / 2, state_chi = chi\<rparr>
        in Some (state # states) }}" |

  "step _ _ = return_pmf None"

fun result :: "trace option \<Rightarrow> nat option" where
  "result (Some (\<lparr>state_p = p, state_chi = chi\<rparr> # _)) =
    Some (nat \<lfloor>(card chi :: real) / p\<rfloor>)" |

  "result _ = None"

definition estimate_size :: "nat list \<Rightarrow> nat option pmf" where
  "estimate_size xs =
    (initial_trace |> foldM_pmf step xs |> map_pmf result)"

end