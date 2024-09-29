theory Final

imports
  "Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF"
begin

(* The geometric PMF in Isabelle starts from 0,
  i.e., it counts the number of failed trials *)
term "geometric_pmf"
(* This is the eager distribution we will work with
   TODO: generalize this later to any p *)
term "replicate_pmf n (geometric_pmf (1/2))"

definition geom_rand::"'a list \<Rightarrow> ('a \<times> nat) list pmf"
  where "geom_rand ls =
    map_pmf (zip ls) (replicate_pmf (length ls) (geometric_pmf (1/2)))"

(* First, define a non-deterministic algorithm *)
definition nondet_geom_aux :: "nat \<Rightarrow> ('a \<times> nat) list \<Rightarrow> 'a set"
  where "nondet_geom_aux k ls =
    {x. case map_of (rev ls) x of None \<Rightarrow> False | Some v \<Rightarrow> k \<le> v}"

definition nondet_geom :: "nat \<Rightarrow> 'a list \<Rightarrow>'a set pmf"
  where "nondet_geom k ls =
     map_pmf (nondet_geom_aux k) (geom_rand ls)"

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
  where "eager_geom_step thresh (x,g) (k,X) = (
    let X = fmdrop x X in
    if g < k then (k,X)
    else fix_k thresh k (fmupd x g X)
  )"

abbreviation eager_geom_aux where 
  "eager_geom_aux thresh st ls \<equiv> fold (eager_geom_step thresh) ls st"

(* The eager estimation algorithm *)
definition eager_geom :: "nat \<Rightarrow> 'a list \<Rightarrow> (nat \<times> ('a \<Rightarrow>\<^sub>F nat)) \<Rightarrow> (nat \<times> ('a \<Rightarrow>\<^sub>F nat)) pmf"
  where "eager_geom thresh ls st = (
    map_pmf (eager_geom_aux thresh st) (geom_rand ls)
  )"

end