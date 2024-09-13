theory Basic_Props_Common

imports
  CVM.Basic_Algo
  CVM.Utils_Approx_Algo

begin

locale basic_props_common = approx_algo + basic_algo +
  assumes threshold_pos : \<open>threshold > 0\<close>

end