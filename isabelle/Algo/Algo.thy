theory Algo

imports
  HOL.Option
  "HOL-Library.Pattern_Aliases"
  "HOL-Probability.Product_PMF"
  (* Frequency_Moments.Frequency_Moments *)
  CVM.Utils
  Params

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

    remove_x_from_chi \<leftarrow> bernoulli_pmf p;
    let chi = (chi
      |> flip (-) {x}
      |> if remove_x_from_chi then id else insert x);

    keep_in_chi :: nat \<Rightarrow> bool \<leftarrow>
      Pi_pmf chi False (\<lambda> _. bernoulli_pmf ((1 :: real) / 2));

    return_pmf (
      if card chi = 0
      then None
      else
        let state =
          \<lparr> state_p = p / 2,
            state_chi = Set.filter keep_in_chi chi \<rparr>
        in Some (state # states)) }" |

  "step _ _ = return_pmf None"

end

end