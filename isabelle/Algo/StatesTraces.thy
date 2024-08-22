theory StatesTraces

imports
  HOL.Real
  (* "HOL-Analysis.Analysis"
  "HOL-Probability.Probability_Measure" *)

begin

record state =
  state_p :: real
  state_chi :: "nat set"

type_synonym trace = "state list"

class well_formed =
  fixes well_formed :: "'a \<Rightarrow> bool"

class well_formed_wrt =
  fixes well_formed_wrt :: "nat \<Rightarrow> 'a \<Rightarrow> bool"

instantiation state_ext :: (type) well_formed_wrt
begin
  fun well_formed_wrt_state where
    "well_formed_wrt_state threshold \<lparr>state_p = p, state_chi = \<chi>\<rparr> =
      (p \<in> {0 <.. 1} \<and> card \<chi> < threshold)"

  instance ..
end

instantiation "list" :: (type) well_formed_wrt
begin
  abbreviation well_formed_wrt_list where
    "well_formed_wrt_list \<equiv> list_all \<circ> well_formed_wrt"

  instance ..
end

end