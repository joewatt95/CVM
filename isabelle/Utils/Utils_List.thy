theory Utils_List

imports
  CVM.Utils_Function

begin

definition least_index :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> nat option\<close> where
  \<open>least_index xs x \<equiv>
    if x \<in> set xs
    then Some <| LEAST index. xs ! index = x
    else None\<close>

lemma least_index_le_length :
  assumes \<open>least_index xs x = Some index\<close>
  shows \<open>index < length xs\<close> 

  by (metis (mono_tags, lifting) assms in_set_conv_nth least_index_def linorder_less_linear not_less_Least option.discI option.inject order_less_trans)

definition greatest_index :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> nat option\<close> where
  \<open>greatest_index xs \<equiv> (xs |> rev |> least_index)\<close>

lemma greatest_index_le_length :
  assumes \<open>greatest_index xs x = Some index\<close>
  shows \<open>index < length xs\<close>

  using assms
  by (metis greatest_index_def least_index_le_length length_rev) 

lemma greatest_index_altdef :
  \<open>greatest_index xs x = (
    if x \<in> set xs
    then Some <| LEAST index. xs ! (length xs - Suc index) = x
    else None)\<close>

  apply (simp add: greatest_index_def least_index_def)
  by (smt (verit, ccfv_threshold) rev_nth LeastI_ex in_set_conv_nth length_rev linorder_less_linear not_less_Least order_le_less_trans order_less_trans set_rev)

end