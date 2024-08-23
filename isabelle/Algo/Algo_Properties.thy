theory Algo_Properties

imports
  CVM.Algo_Main

begin

context params begin

lemma initial_state_well_formed :
  "\<turnstile> initial_state ok"
  apply simp
  sorry

lemma estimate_size_empty [simp] :
  "estimate_size [] = return_pmf (Some 0)"
  sorry

end

end