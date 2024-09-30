theory Final

imports
  "Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF"
begin

(* The geometric PMF in Isabelle starts from 0,
  i.e., it counts the number of failed trials *)
term "geometric_pmf"

(* This is the eager distribution we will work with
   TODO: we can generalize this later to any p *)
term "replicate_pmf n (geometric_pmf (1/2))"

definition geom_rand::"'a list \<Rightarrow> ('a \<times> nat) list pmf"
  where "geom_rand ls =
    map_pmf (zip ls)
      (replicate_pmf (length ls) (geometric_pmf (1/2)))"

(* First, define a non-deterministic algorithm *)
definition nondet_geom_aux :: "nat \<Rightarrow> ('a \<times> nat) list \<Rightarrow> 'a set"
  where "nondet_geom_aux k ls =
    {x. case map_of (rev ls) x of None \<Rightarrow> False | Some v \<Rightarrow> k \<le> v}"

definition nondet_geom :: "nat \<Rightarrow> 'a list \<Rightarrow>'a set pmf"
  where "nondet_geom k ls =
     map_pmf (nondet_geom_aux k) (geom_rand ls)"

definition update_X:: "nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow>
  ('a \<Rightarrow>\<^sub>F nat) \<Rightarrow> ('a \<Rightarrow>\<^sub>F nat)" where
  "update_X k x g X = (
    let X = fmdrop x X in
    if g < k then X
    else fmupd x g X)"

(* This can be changed to be recursive (?) *)
definition fix_k :: "nat \<Rightarrow> nat \<Rightarrow>
    ('a \<Rightarrow>\<^sub>F nat) \<Rightarrow> (nat \<times> ('a \<Rightarrow>\<^sub>F nat))" where
  "fix_k thresh k X = (
    if size X < thresh then (k,X)
    else
      let k = k + 1 in
      let X = fmrestrict_set {x. k \<le> X x} X in
      (k,X)
  )"
 
fun eager_geom_step :: "nat \<Rightarrow> ('a \<times> nat) \<Rightarrow>
    nat \<times> ('a \<Rightarrow>\<^sub>F nat) \<Rightarrow>
    nat \<times> ('a \<Rightarrow>\<^sub>F nat)"
  where "eager_geom_step thresh (x,g) (k,X) =
    fix_k thresh k (update_X k x g X)"

abbreviation eager_geom_aux where 
  "eager_geom_aux thresh st ls \<equiv> fold (eager_geom_step thresh) ls st"

(* The eager estimation algorithm *)
definition eager_geom :: "nat \<Rightarrow> 'a list \<Rightarrow> (nat \<times> ('a \<Rightarrow>\<^sub>F nat)) \<Rightarrow> (nat \<times> ('a \<Rightarrow>\<^sub>F nat)) pmf"
  where "eager_geom thresh ls st = (
    map_pmf (eager_geom_aux thresh st) (geom_rand ls)
  )"

lemma nondet_geom_aux_snoc:
  shows "nondet_geom_aux k (xs @ [(x,g)]) = (
    if g < k then  Set.remove x (nondet_geom_aux k xs)
    else insert x (nondet_geom_aux k xs))"
  unfolding nondet_geom_aux_def
  by auto

lemma update_X_eq:
  assumes "update_X k x g X = X'"
  assumes "fmdom' X = nondet_geom_aux k xs"
  shows "fmdom' X' = nondet_geom_aux k (xs @ [(x,g)])"
  using assms
  unfolding update_X_def Let_def 
  apply (auto split:if_splits)
  unfolding nondet_geom_aux_snoc
  by auto

lemma fix_k_eq:
  assumes "fix_k thresh k X  = (k',X')"
  assumes "fmdom' X = nondet_geom_aux k xs"
  shows "fmdom' X' = nondet_geom_aux k' xs"
  using assms
  unfolding fix_k_def Let_def nondet_geom_aux_def
  (* probably splitting too fast *)
  apply (auto split:if_splits simp add: fmdom'_restrict_set_precise)
  sorry

lemma eager_geom_step_eq:
  assumes "eager_geom_step thresh (x,g) (k,X) = (k',X')"
  assumes "fmdom' X = nondet_geom_aux k xs"
  shows "fmdom' X' = nondet_geom_aux k' (xs @ [(x,g)])"
  using assms
  by (simp add: fix_k_eq update_X_eq)

lemma eager_geom_aux_eq:
  assumes "eager_geom_aux thresh (k,X) ls = (k',X')"
  assumes "fmdom' X = nondet_geom_aux k xs"
  shows "fmdom' X' = nondet_geom_aux k' (xs @ ls)"
  using assms
proof (induction ls arbitrary: k X k' X' xs)
  case Nil
  then show ?case
    by auto
next
  case ih:(Cons xg ls)
  obtain k'' X'' where
    *: "eager_geom_step thresh xg (k, X) = (k'',X'')"
     by fastforce
  show ?case
    using ih(2)
    apply (clarsimp simp add: *)
    apply (drule ih(1)[where xs="xs @ [xg]"])
    apply (metis "*" eager_geom_step.simps fix_k_eq ih(3) prod.exhaust update_X_eq)
    by clarsimp
qed

lemma eager_geom_aux_eq':
  assumes "eager_geom_aux thresh (0,fmempty) ls = (k,X)"
  shows "fmdom' X = nondet_geom_aux k ls"
  using assms
  apply (rule eager_geom_aux_eq[where xs="[]",simplified])
  by (auto simp add: nondet_geom_aux_def)

lemma rel_pmf_eager_geom_nondet_geom:
  "rel_pmf (\<lambda>(k,X) Y. k = K \<longrightarrow> fmdom' X = Y) (eager_geom thresh ls (0,fmempty)) (nondet_geom K ls)"
  unfolding eager_geom_def nondet_geom_def pmf.rel_map
  apply (intro rel_pmf_reflI)
  by (clarsimp simp add: eager_geom_aux_eq')

end