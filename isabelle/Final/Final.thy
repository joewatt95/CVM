theory Final

imports
  "Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF"
  "Monad_Normalisation.Monad_Normalisation"
begin

(* The geometric PMF in Isabelle starts from 0,
  i.e., it counts the number of failed trials *)
term "geometric_pmf p"

(* This is the eager distribution we will work with
   TODO: we can generalize this later to any p *)
term "replicate_pmf n (geometric_pmf (1/2))"

definition geom_rand::"'a list \<Rightarrow> ('a \<times> nat) list pmf"
  where "geom_rand ls =  
    map_pmf (zip ls)
      (replicate_pmf (length ls) (geometric_pmf (1/2)))"

(* Identical to remdups but removes on fst projection *)
fun remdups1 :: "('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "remdups1 [] = []" |
  "remdups1 (x # xs) = (if fst x \<in> fst ` set xs then remdups1 xs else x # remdups1 xs)"

lemma remdups1_rev_map_of:
  shows "map_of (rev ls) = map_of (remdups1 ls)"
  apply (induction ls)
  apply (auto simp add: fun_eq_iff dom_map_of_conv_image_fst map_add_dom_app_simps(3) map_add_upd_left)
  by (metis (mono_tags, lifting) fun_upd_def map_add_None map_add_Some_iff option.collapse set_rev weak_map_of_SomeI)

definition nondet_geom_aux :: "nat \<Rightarrow> ('a \<times> nat) list \<Rightarrow> 'a set"
  where "nondet_geom_aux k ls =
  {x.
    case map_of (rev ls) x of
      None \<Rightarrow> False | Some v \<Rightarrow> k \<le> v}"

lemma remdups1_distinct_map_fst:
  shows "distinct (map fst (remdups1 xs))"
  apply (induction xs)
  apply auto
  by (metis dom_map_of_conv_image_fst fst_conv image_eqI remdups1_rev_map_of set_rev)

lemma nondet_geom_aux_eq_filter_remdups1:
  shows "nondet_geom_aux k ls =
    fst ` set (filter (\<lambda>(y, v). k \<le> v) (remdups1 ls))"
  unfolding nondet_geom_aux_def remdups1_rev_map_of
  apply (auto simp add: set_eq_iff image_def remdups1_distinct_map_fst)
  by (metis (no_types, opaque_lifting) Domain.simps Domain_fst domIff dom_map_of_conv_image_fst map_of_SomeD option.case(2) option.simps(4) weak_map_of_SomeI)

definition nondet_geom :: "nat \<Rightarrow> 'a list \<Rightarrow>'a set pmf"
  where "nondet_geom k ls =
     map_pmf (nondet_geom_aux k) (geom_rand ls)"

definition update_X:: "nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow>
  ('a \<times> nat) list \<Rightarrow> ('a \<times> nat) list" where
  "update_X k x g X = (
    let X = filter (\<lambda>(y,v). y \<noteq> x) X in
    if g < k then X
    else X @ [(x,g)])"

definition fix_k :: "nat \<Rightarrow> nat \<Rightarrow>
  ('a \<times> nat) list \<Rightarrow> (nat \<times> ('a \<times> nat) list)" where
  "fix_k thresh k X = (
    if length X < thresh then (k,X)
    else
      let k = k + 1 in
      let X = filter (\<lambda>(y,v). k \<le> v) X in
      (k,X)
  )"
 
fun eager_geom_step :: "nat \<Rightarrow> ('a \<times> nat) \<Rightarrow>
    nat \<times> ('a \<times> nat) list \<Rightarrow>
    nat \<times> ('a \<times> nat) list"
  where "eager_geom_step thresh (x,g) (k,X) =
    fix_k thresh k (update_X k x g X)"

abbreviation eager_geom_aux where 
  "eager_geom_aux thresh st ls \<equiv>
    fold (eager_geom_step thresh) ls st"

(* The eager estimation algorithm *)
definition eager_geom :: "nat \<Rightarrow> 'a list \<Rightarrow>
  (nat \<times> 'a set) pmf"
  where "eager_geom thresh ls = (
    map_pmf ( (\<lambda>(k,X). (k, fst ` set X)) \<circ> eager_geom_aux thresh (0,[])) (geom_rand ls)
  )"

lemma remdups1_snoc:
  shows "remdups1 (xs @ [(x,g)]) = filter (\<lambda>(y,v). y \<noteq> x) (remdups1 xs) @ [(x,g)]"
  apply (induction xs)
   by auto

lemma update_X_eq:
  assumes "update_X k x g X = X'"
  assumes "X = filter (\<lambda>(y,v). k \<le> v) (remdups1 xs)"
  shows "X' = filter (\<lambda>(y,v). k \<le> v) (remdups1 (xs @ [(x,g)]))"
  using assms
  unfolding update_X_def Let_def 
  apply (auto split:if_splits simp add: remdups1_snoc)
  by meson+

lemma fix_k_eq:
  assumes "fix_k thresh k X = (k',X')"
  assumes "X = filter (\<lambda>(y,v). k \<le> v) (remdups1 xs)"
  shows "X' = filter (\<lambda>(y,v). k' \<le> v) (remdups1 xs)"
  using assms
  unfolding fix_k_def Let_def
  (* probably splitting too fast *)
  apply (auto split:if_splits)
  by (metis Suc_leD case_prodE case_prodI2 prod.sel(2))

lemma eager_geom_step_eq:
  assumes "eager_geom_step thresh (x,g) (k,X) = (k',X')"
  assumes "X = filter (\<lambda>(y,v). k \<le> v) (remdups1 xs)"
  shows "X' = filter (\<lambda>(y,v). k' \<le> v) (remdups1 (xs @ [(x,g)]))"
  using assms
  by (simp add: fix_k_eq update_X_eq)

lemma eager_geom_aux_eq:
  assumes "eager_geom_aux thresh (k,X) ls = (k',X')"
  assumes "X = filter (\<lambda>(y,v). k \<le> v) (remdups1 xs)"
  shows "X' = filter (\<lambda>(y,v). k' \<le> v) (remdups1 (xs @ ls))"
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
  assumes "eager_geom_aux thresh (0,[]) ls = (k,X)"
  shows "fst ` set X = nondet_geom_aux k ls"
  using eager_geom_aux_eq[where xs="[]",simplified, OF assms]
  by (metis nondet_geom_aux_eq_filter_remdups1)

lemma rel_pmf_eager_geom_nondet_geom:
  "rel_pmf (\<lambda>(k,X) Y. k = K \<longrightarrow> X = Y)
    (eager_geom thresh ls) (nondet_geom K ls)"
  unfolding eager_geom_def nondet_geom_def pmf.rel_map
  apply (intro rel_pmf_reflI)
  using eager_geom_aux_eq'
  by (metis (mono_tags, lifting) case_prod_beta' comp_apply split_pairs)

lemma eager_geom_nondet_geom_measureD:
  shows "
  measure_pmf.prob (eager_geom thresh ls)
    {kX. fst kX = K \<and> P (snd kX)} \<le>
  measure_pmf.prob (nondet_geom K ls) {Y. P Y}"
proof -
  have "
    measure_pmf.prob (eager_geom thresh ls)
      {kX. fst kX = K \<and> P (snd kX)} \<le>
    measure_pmf.prob (nondet_geom K ls)
      {y. \<exists>x\<in>{kX. fst kX = K \<and> P (snd kX)}.
             (case x of (k, X) \<Rightarrow> \<lambda>Y. k = K \<longrightarrow> X = Y) y}"
    using rel_pmf_measureD[OF rel_pmf_eager_geom_nondet_geom] .
  also have "... = measure_pmf.prob (nondet_geom K ls) {Y. P Y}"
    apply (intro arg_cong[where f = "measure_pmf.prob (nondet_geom K ls)"])
    by auto
  finally show ?thesis .
qed

(* copied from rel_spmf_bindI1 *)
lemma rel_pmf_bindI1:
  assumes f: "\<And>x. x \<in> set_pmf p \<Longrightarrow> rel_pmf R (f x) q"
  shows "rel_pmf R (bind_pmf p f) q"
proof -
  fix x :: 'a
  have "rel_pmf R (bind_pmf p f) (bind_pmf (return_pmf x) (\<lambda>_. q))"
    by(rule rel_pmf_bindI[where R="\<lambda>x _. x \<in> set_pmf p"])(simp_all add: rel_pmf_return_pmf2 f)
  then show ?thesis by simp
qed

(* copied from rel_spmf_bindI2 *)
lemma rel_pmf_bindI2:
  "\<lbrakk> \<And>x. x \<in> set_pmf q \<Longrightarrow> rel_pmf R p (f x) \<rbrakk>
  \<Longrightarrow> rel_pmf R p (bind_pmf q f)"
  using rel_pmf_bindI1[of q "conversep R" f p]
  by(simp add: pmf.rel_conversep)

lemma map_pmf_cons_eq:
  shows "map_pmf (\<lambda>ls. c # f ls) p =
    map_pmf (\<lambda>ls. c # ls) (map_pmf f p)"
  by (simp add: map_pmf_comp)
    
lemma remdups1_replicate_pmf:
  shows"
  map_pmf (zip (remdups ls)) (replicate_pmf (length (remdups ls)) p) =
  map_pmf (remdups1 \<circ> zip ls) (replicate_pmf (length ls) p)"
  including monad_normalisation
  apply (induction ls)
  subgoal
    by auto
  apply (auto simp add:map_pmf_def)
  subgoal for x ls
    apply (subst pmf.rel_eq[symmetric])
    apply (intro rel_pmf_bindI2[of p])
    apply (clarsimp simp add: pmf.rel_eq map_pmf_def[symmetric])
    apply (intro pmf.map_cong0)
    apply auto
    by (metis (mono_tags, lifting) list.set_map map_fst_zip mem_Collect_eq set_replicate_pmf)
  subgoal for x ls
    apply (subst pmf.rel_eq[symmetric])
    apply (intro rel_pmf_bindI[of "(=)" p])
     apply (simp add: pmf.rel_eq)
    apply (clarsimp simp add: pmf.rel_eq map_pmf_def[symmetric])
    apply (subst  map_pmf_cons_eq)
    apply (simp add: map_pmf_comp)
    apply (intro pmf.map_cong0)
    using set_zip_leftD by fastforce
  done

lemma Pi_pmf_map_of_replicate_pmf:
  assumes "distinct ls"
  shows "
    Pi_pmf (set ls) None (\<lambda>_. map_pmf Some p) =
    map_pmf (map_of \<circ> zip ls) (replicate_pmf (length ls) p)"
  including monad_normalisation
  using assms
  apply (induction ls)
   apply auto
  apply (subst Pi_pmf_insert')
  by (auto simp add: map_pmf_def)

(* TODO: extend this calculation more to reach
  a desirable final PMF to analyze *)
lemma nondet_geom_eq:
  "nondet_geom k ls =
   map_pmf
     (\<lambda>m. {x. case m x of None \<Rightarrow> False | Some x \<Rightarrow> k \<le> x})
     (Pi_pmf (set ls) None (\<lambda>_. map_pmf Some (geometric_pmf (1 / 2))))"
proof -
  have "nondet_geom k ls =
  map_pmf
  (\<lambda>ls. {x. case map_of ls x of None \<Rightarrow> False
                | Some x \<Rightarrow> k \<le> x})
  (map_pmf (remdups1 \<circ> zip ls)
       (replicate_pmf (length ls) (geometric_pmf (1 / 2))))"
  unfolding nondet_geom_def nondet_geom_aux_def
    geom_rand_def remdups1_rev_map_of pmf.map_comp
  by (auto simp add: o_def)
  also have "... =
    map_pmf
     (\<lambda>m. {x. case m x of None \<Rightarrow> False | Some x \<Rightarrow> k \<le> x})
     (map_pmf (map_of \<circ> zip (remdups ls))
       (replicate_pmf (length (remdups ls))
         (geometric_pmf (1 / 2))))"
    unfolding remdups1_replicate_pmf[symmetric] 
    by (auto simp add: map_pmf_comp)
  also have "... =
     map_pmf
     (\<lambda>m. {x. case m x of None \<Rightarrow> False | Some x \<Rightarrow> k \<le> x})
     (Pi_pmf (set ls) None (\<lambda>_. map_pmf Some (geometric_pmf (1 / 2))))"
    apply (subst Pi_pmf_map_of_replicate_pmf[symmetric])
    by auto
  finally show ?thesis  .
qed

lemma nondet_geom_eq_Pi_pmf:
  "nondet_geom k ls =
    map_pmf Collect (Pi_pmf (set ls) False (\<lambda>_. bernoulli_pmf (1/2^k)))"
  apply (induction ls)
  apply (auto simp add: nondet_geom_def geom_rand_def  nondet_geom_aux_eq_filter_remdups1)

end