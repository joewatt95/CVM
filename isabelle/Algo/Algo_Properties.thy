theory Algo_Properties

imports
  CVM.Algo_Basic

begin

context params begin

lemma estimate_size_empty [simp] :
  "estimate_size [] = return_pmf (Some 0)"
  by simp

thm well_formed.induct

lemma initial_trace_well_formed :
  "\<turnstile> initial_trace ok"
  by (simp add: singleton)

lemma prob_always :
  assumes "P x"
  shows "AE x' in return_pmf x. P x'"
  by (simp add: AE_measure_pmf_iff assms)

(* https://www.cse.unsw.edu.au/~kleing/papers/Cock_KS_08.pdf *)
lemma prob_seq :
  assumes
    "\<And>x. P x \<Longrightarrow> AE y in f x. Q y" and
    "\<And>y. Q y \<Longrightarrow> AE z in g y. R z"
  shows
    "\<And>x. P x \<Longrightarrow> AE z in f x \<bind> g. R z"
proof -
  fix x assume "P x"
  then have "AE y in f x. Q y" by (simp add: assms(1)) 
  then show "AE z in f x \<bind> g. R z" sorry
qed

lemma prob_loop :
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b pmf"
  assumes
    "P val" and
    "\<And>x val. P val \<Longrightarrow> AE val' in f x val. P val'"
  shows "AE val' in foldM_pmf f xs val. P val'"
proof (induction xs)
  case Nil
  then show ?case by (metis assms(1) foldM_pmf.simps(1) prob_always)
next
  case (Cons x xs)
  then have "AE val' in foldM_pmf f xs val. P val'" by simp
  moreover have "
    (AE val' in foldM_pmf f (x # xs) val. P val') =
    (AE val' in bind_pmf (f x val) (foldM_pmf f xs). P val')"
    by (metis foldM_pmf.simps(2))
  ultimately show ?case sorry
qed

lemma step_with_trace_size :
  "AE states' in step_with_trace x states.
    states' = states \<or> (\<exists> state'. states' = state' # states)"
proof (induction states arbitrary: x)
  case Nil
  then have "step_with_trace x [] = return_pmf []" by simp
  then show ?case sorry
next
  case (Cons a states)
  then show ?case sorry
qed

(*
\<turnstile> [states ok] states' \<leftarrow> step_with_trace x states [states' ok]
*)
lemma step_preserves_well_formedness : "
  \<turnstile> states ok \<Longrightarrow> AE states' in step_with_trace x states. \<turnstile> states' ok"
proof (induction rule: well_formed.induct)
  case nil
  then show ?case
    by (metis prob_always step_with_trace.simps(2) well_formed.nil)
next
  case (singleton state)
  then show ?case
  proof (cases state)
    case None
    then have "step_with_trace x [None] = return_pmf [None]"
      using local.singleton by simp
    then show ?thesis by (metis None prob_always well_formed.singleton)
  next
    case (Some state')
    then show ?thesis sorry
  qed
next
  case (some_some state' state states)
  then show ?case sorry
next
  case (none_some state states)
  then show ?case sorry
qed

lemma test' : "
 \<P>(states' in run_steps_with_trace x states. \<turnstile> states' ok) = 1"
 sorry

end

end