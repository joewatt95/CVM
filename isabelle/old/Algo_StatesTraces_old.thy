theory Algo_StatesTraces_old

imports
  HOL.Real

begin

record 'a ok_state =
  state_p :: real
  state_chi :: "'a set"

type_synonym 'a state = "'a ok_state option"

type_synonym 'a trace = "'a state list"

(* class well_formed =
  fixes well_formed :: "'a \<Rightarrow> bool"

class is_failure =
  fixes is_failure :: "'a \<Rightarrow> bool" *)

inductive well_formed_trace :: "'a trace \<Rightarrow> bool" ("\<turnstile> _ wf" [60]) where
  nil : "\<turnstile> [] wf" |
  singleton : "\<turnstile> [state] wf" |
  some_some : "\<turnstile> states wf \<Longrightarrow> \<turnstile> Some state' # Some state # states wf" |
  none_some : "\<turnstile> states wf \<Longrightarrow> \<turnstile> None # Some state # states wf"

inductive failed_trace :: "'a trace \<Rightarrow> bool" ("\<turnstile> _ failed" [60]) where "
  \<turnstile> None # xs wf \<Longrightarrow> \<turnstile> None # xs failed"

(* class well_formed_wrt =
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