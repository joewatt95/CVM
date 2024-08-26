theory Algo_StatesTraces

imports
  HOL.Real

begin

record 'a state =
  state_p :: real
  state_chi :: "'a set"

type_synonym 'a trace = "'a state option list"

(* class well_formed =
  fixes well_formed :: "'a \<Rightarrow> bool"

class well_formed_wrt =
  fixes well_formed_wrt :: "nat \<Rightarrow> 'a \<Rightarrow> bool" *)

(* instantiation ('a state_ext) :: (type) well_formed_wrt
begin
  fun well_formed_wrt_state where
    "well_formed_wrt_state threshold \<lparr>state_p = p, state_chi = \<chi>\<rparr> =
      (p \<in> {0 <.. 1} \<and> card \<chi> < threshold)"

  instance ..
end

instantiation "list" :: (type) well_formed_wrt
begin
  definition well_formed_wrt_list where
    [simp] : "well_formed_wrt_list \<equiv> list_all \<circ> well_formed_wrt"

  instance ..
end *)


end