theory Algo_Properties

imports
  CVM.Algo_Main

begin

lemma estimate_size_empty [simp] :
  "estimate_size [] = return_pmf (Some 0)"
  sorry

end