theory CVM_Algo_Nondet

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Utils_Approx_Algo
  CVM_Algo_Lazy_Eager

begin

(* After processing the list xs, the chi is the set of
     distinct elements x in xs where the last time
     we flipped coins for x, the first k elements were heads. *)
definition nondet_alg_aux ::
  "nat \<Rightarrow> 'a list \<Rightarrow> coin_matrix \<Rightarrow> 'a set" where
  "nondet_alg_aux k xs \<phi> =
    {x \<in> set xs. \<forall> k' < k. curry \<phi> k' (last_index xs x)}"

end