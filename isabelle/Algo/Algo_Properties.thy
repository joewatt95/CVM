theory Algo_Properties

imports
  CVM.Algo_Basic

begin

context params begin

lemma estimate_size_empty [simp] :
  "estimate_size [] = return_pmf (Some 0)"
  by simp

(* thm well_formed_trace.induct *)

lemma initial_trace_well_formed :
  "\<turnstile> initial_trace wf"
  by (simp add: singleton)

lemma prob_always :
  fixes P M
  assumes "\<And>x. x \<in> space M \<Longrightarrow> P x"
  shows "AE x in M. P x"
  by (simp add: assms)

lemma prob_return :
  fixes P x
  assumes "P x"
  shows "AE x' in return_pmf x. P x'"
  by (simp add: AE_measure_pmf_iff assms)

(*
https://www.cse.unsw.edu.au/~kleing/papers/Cock_KS_08.pdf
https://moves.rwth-aachen.de/wp-content/uploads/SS15/vpp/VPP-Lecture-04.pdf
 *)
lemma prob_seq :
  fixes
    f :: "'a \<Rightarrow>'b pmf" and
    g :: "'b \<Rightarrow>'c pmf"
  assumes
    "\<And>x. P x \<Longrightarrow> AE y in f x. Q y" and
    "\<And>y. Q y \<Longrightarrow> AE z in g y. R z"
  shows
    "\<And>x. P x \<Longrightarrow> AE z in bind_pmf (f x) g. R z"
proof -
  fix x assume "P x"
  then have "AE y in f x. Q y" by (simp add: assms(1)) 
  then show "AE z in bind_pmf (f x) g. R z" sorry

  (* then
    show "AE z in bind_pmf (f x) g. R z"
    when "\<And>z. z \<in> bind_pmf (f x) g \<Longrightarrow> R z"
    using AE_pmfI that by blast

  then show "\<And>z. z \<in> bind_pmf (f x) g \<Longrightarrow> R z"
  proof -
    fix z assume "z \<in> bind_pmf (f x) g" 
    then have "measure (bind_pmf (f x) g) {z} \<noteq> 0"
      by (simp add: set_pmf.rep_eq)   
    then show "R z" sorry
  qed *)
qed

lemma prob_loop :
  fixes f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b pmf"
  assumes
    "P val" and
    "\<And>x val. P val \<Longrightarrow> AE val' in f x val. P val'"
  shows "AE val' in foldM_pmf f xs val. P val'"
proof (induction xs)
  case Nil
  then show ?case by (metis assms(1) foldM_pmf.simps(1) prob_return)
next
  case (Cons x xs)
  then have "AE val' in foldM_pmf f xs val. P val'" by simp
  moreover have "
    (AE val' in foldM_pmf f (x # xs) val. P val') =
    (AE val' in bind_pmf (f x val) (foldM_pmf f xs). P val')"
    by (metis foldM_pmf.simps(2))
  ultimately show ?case sorry
qed

(* lemma prob_loop_fail_lt :
  fixes
    f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b option pmf" and
    P :: "'b \<Rightarrow> bool" and
    val :: "'b"
  assumes
    "P val" and "\<And>x val. P val \<Longrightarrow> AE val' in f x val. P val'" and
    "P val \<Longrightarrow> \<P>(val' in f x val. val' = None) \<le> \<alpha>"
  shows "\<P>(val' in foldM_option_pmf f xs val. val' = None) \<le> \<alpha> ^ length xs"
proof -
  show ?thesis sorry
qed *)

term measure_pmf.prob
term pmf
term set_pmf

lemma aux' :
  fixes
    x :: "'a" and
    f :: "'a pmf"
  shows "\<P>(x' in f. x = x') = pmf f x"
  by (simp add: measure_pmf_single)

lemma aux'' :
  fixes
    f :: "'a pmf" and
    P :: "'a \<Rightarrow> bool"
  shows "
    (\<forall> a. P a \<longrightarrow> pmf f a = p) =
    (\<P>(a in f. P a) = p)"
  sorry

(* lemma aux'' :
  fixes
    x :: "'a option pmf" and
    f :: "'a \<Rightarrow> 'a option pmf"
  assumes "\<And> a. \<P>(a' in f a. a' = None) \<le> \<alpha>" 
  shows "\<P>(x' in x \<bind> case_option (return_pmf None) f. x = None) \<le> pmf x None + \<alpha>"
proof -
  show ?thesis sorry
qed *)

lemma aux :
  fixes
    x :: "'a option pmf" and
    f :: "'a \<Rightarrow> 'a option pmf"
  assumes "\<And> a. Some a \<in> set_pmf x \<Longrightarrow> pmf (f a) None \<le> \<alpha>"
  shows "pmf (x \<bind> case_option (return_pmf None) f) None \<le> pmf x None + \<alpha>"
proof -
  show ?thesis sorry
qed

lemma prob_loop_fail_lt' :
  fixes
    f :: "'a \<Rightarrow> 'b \<Rightarrow> 'b option pmf" and
    P :: "'b \<Rightarrow> bool"
  assumes
    "\<And>x val val'. \<lbrakk>P val; Some val' \<in> set_pmf (f x val)\<rbrakk> \<Longrightarrow> P val'" and
    "\<And> x val. P val \<Longrightarrow> pmf (f x val) None \<le> \<alpha>"
  shows "\<And> val. P val \<Longrightarrow> pmf (foldM_option_pmf f xs val) None \<le> \<alpha> * length xs"
proof (induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons x xs)
  then have "pmf (foldM_option_pmf f (x # xs) val) None \<le> pmf (f x val) None + \<alpha> * length xs"
     using assms(1) by (auto simp add: intro!: aux)
  then show ?case
    by (simp add: Cons.prems assms(2) distrib_left order_trans)
qed

(* lemma step_with_trace_size :
  "AE states' in step_with_trace x states.
    states' = states \<or> (\<exists> state'. states' = state' # states)"
proof (induction states arbitrary: x)
  case Nil
  then have "step_with_trace x [] = return_pmf []" by simp
  then show ?case sorry
next
  case (Cons a states)
  then show ?case sorry
qed *)

lemma step_preserves_well_formedness : "
  \<turnstile> states wf \<Longrightarrow> AE states' in step_with_trace x states. \<turnstile> states' wf"
proof (induction rule: well_formed_trace.induct)
  case nil
  then show ?case
    by (metis prob_return step_with_trace.simps(2) well_formed_trace.nil)
next
  case (singleton state)
  then show ?case
  proof (cases state)
    case None
    then have "step_with_trace x [None] = return_pmf [None]"
      using local.singleton by simp
    then show ?thesis by (metis None prob_return well_formed_trace.singleton)
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

lemma test : "
  AE states' in run_steps_with_trace xs states.
    \<turnstile> states' wf \<and> length states' \<le> length xs"
 sorry

(* lemma test' : "
  AE states' in run_steps_with_trace xs states.
    \<turnstile> states' failed \<longrightarrow> True"
 sorry *)

end

end