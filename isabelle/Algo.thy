theory Algo

imports
  HOL.Option
  "HOL-Library.Pattern_Aliases"
  "HOL-Probability.Probability_Mass_Function"
  (* Frequency_Moments.Frequency_Moments *)
  CVM_Utils.CVM_Function
  Params
  StatesTraces

begin

context includes pattern_aliases begin

definition initial_state where
  "initial_state \<equiv> \<lparr>state_p = 1, state_chi = {}\<rparr>"

(* lemma (in params) initial_state_well_formed :
  "well_formed initial_state"
  sorry *)

fun step :: "trace option \<Rightarrow> nat \<Rightarrow> trace option pmf" where
  "step (Some (state # _ =: states)) x = do {
    let chi = state_chi state;
    let p = state_p state;
    b \<leftarrow> bernoulli_pmf p;
    let chi0 = (chi
      |> flip (-) {x}
      |> if b then id else insert x);
    undefined }" |

  "step _ _ = return_pmf None"

end

end