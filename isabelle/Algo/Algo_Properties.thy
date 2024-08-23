theory Algo_Properties

imports
  CVM.Algo_Main

begin

context params begin

lemma initial_state_well_formed :
  "\<turnstile> initial_state ok"
  apply simp
  sorry

lemma step_preserves_well_formedness :
  assumes
    "\<turnstile> state ok" and
    "\<turnstile> state \<rightarrow>[x]\<rightarrow> state'"
  shows
    "\<turnstile> state' ok"
  sorry

lemma test :
  "(card (state_chi state) = threshold) = ⊬ state \<rightarrow>[x]\<rightarrow>"
  sorry

lemma estimate_size_empty [simp] :
  "estimate_size [] = return_pmf (Some 0)"
  sorry

end

end