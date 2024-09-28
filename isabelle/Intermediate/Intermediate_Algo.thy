theory Intermediate_Algo

imports
  CVM.Basic_Algo

begin

definition step :: \<open>'a \<Rightarrow> 'a set list \<Rightarrow> 'a set list pmf\<close> where
  \<open>step x chis \<equiv> do {
    num_heads \<leftarrow> geometric_pmf <| 1 / 2;

    let capped_num_heads = min num_heads (length chis);

    let insert_or_remove = (\<lambda> index.
      if index \<le> capped_num_heads
      then insert x
      else Set.remove x);

    chis |> map_index insert_or_remove |> return_pmf }\<close>

end