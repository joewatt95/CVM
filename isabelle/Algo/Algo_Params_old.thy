theory Algo_Params_old

imports
  HOL.Transcendental
  CVM.Utils_Real
  CVM.Algo_StatesTraces_old

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

lemma threshold_pos :
  "threshold > 0" and
  "threshold \<ge> 1"
proof -
  show "threshold > 0" using m_pos \<epsilon>_in_0_1 \<delta>_in_0_1 by auto
  then show "threshold \<ge> 1" by linarith
qed

(* definition well_formed :: "_::{well_formed_wrt} \<Rightarrow> bool"
  ("\<turnstile> _ ok" [999]) where 
  [simp] : "well_formed \<equiv> well_formed_wrt threshold" *)

end

end