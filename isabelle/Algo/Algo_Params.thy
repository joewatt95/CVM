theory Algo_Params

imports
  HOL.Transcendental
  CVM.Utils_Real
  CVM.Algo_StatesTraces

begin

locale params =
  fixes
    m :: nat and
    \<epsilon> :: real and
    \<delta> :: real
  assumes
    m_pos : "1 \<le> m" and
    \<epsilon>_in_0_1 : "\<epsilon> \<in> {0 <..< 1}" and
    \<delta>_in_0_1 : "\<delta> \<in> {0 <..< 1}"

begin

definition threshold :: nat where
  [simp] : "threshold \<equiv> nat \<lceil>(12 / \<epsilon> ^ 2) * log2 (8 * m / \<delta>)\<rceil>"

lemma threshold_pos : "threshold > 0"
  using m_pos \<epsilon>_in_0_1 \<delta>_in_0_1 by auto

lemma threshold_gt_one : "threshold \<ge> 1"
  using threshold_pos by linarith

definition well_formed :: "_::{well_formed_wrt} \<Rightarrow> bool"
  ("\<turnstile> _ ok" [999]) where 
  [simp] : "well_formed \<equiv> well_formed_wrt threshold"

(* lemma well_formed_def [simp] :
  "well_formed = well_formed_wrt threshold"
  by force *)

end

end