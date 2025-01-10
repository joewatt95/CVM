theory CVM_Algo_Proof
  imports
    CVM_Algo
begin

locale cvm_algo_proof = cvm_algo +
  assumes "f \<in> {1/2..<1}"
begin                       

(* Copied as-is for Lemma 2 *)
context
  fixes \<phi> :: "real \<Rightarrow> bool \<Rightarrow> real"
  assumes pos :"\<And>x b. x \<in> {0<..1} \<Longrightarrow> \<phi> x b \<ge> 0"
  assumes c1: \<open>\<And>\<alpha> x.
    \<alpha> \<in> {0<..<1} \<Longrightarrow> x \<in> {0<..1} \<Longrightarrow>
    (1 - \<alpha>) * \<phi> x False + \<alpha> * \<phi> x True \<le> \<phi> (x / \<alpha>) True \<close>
  assumes c2: "\<And>x y.
    0 < x \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> 1 \<Longrightarrow>
    \<phi> x False \<le> \<phi> y False"
begin

abbreviation (input)
  \<open>aux \<equiv> \<lambda> x state. \<phi> (f ^ (state_k state)) (x \<in> (state_chi state))\<close>

(*
  Intuition:
  - U is the set of elements we have already seen
  - st is the accumulated PMF so far
  - We know:
    state_k st \<le> n where n is the number of list elements
    state_chi st \<subseteq> U
*)

lemma expectation_step1:
  assumes U: "finite U"
  assumes "\<And>S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation stp (prod aux S) \<le> (\<phi> 1 True) ^ card S"
  assumes "S \<subseteq> insert x U"
  shows "
    measure_pmf.expectation (stp \<bind> step1 x) (prod aux S)
      \<le> (\<phi> 1 True) ^ card S"
  sorry

lemma expectation_step2:
  assumes U: "finite U"
  assumes "measure_pmf.expectation stp (prod aux S) \<le> (\<phi> 1 True) ^ card S"
  assumes "S \<subseteq> U"
  shows "
    measure_pmf.expectation (stp \<bind> step2) (prod aux S) \<le> (\<phi> 1 True) ^ card S"
  sorry

lemma expectation_cvm_step:
  assumes U: "finite U"
  assumes "\<And>S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation stp (prod aux S) \<le> (\<phi> 1 True) ^ card S"
  assumes "S \<subseteq> insert x U"
  shows "
    measure_pmf.expectation (stp \<bind> cvm_step x) (prod aux S) \<le> (\<phi> 1 True) ^ card S"
  sorry

lemma expectation_cvm:
  assumes U: "finite U"
  assumes "\<And>S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation stp (prod aux S) \<le> (\<phi> 1 True) ^ card S"
  assumes "S \<subseteq> set xs \<union> U"
  shows "
    measure_pmf.expectation (stp \<bind> cvm xs) (prod aux S) \<le> (\<phi> 1 True) ^ card S"
  sorry

(* Run some prefix of the elements + one more *)
lemma expectation_cvm_step1:
  assumes U: "finite U"
  assumes "\<And>S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation stp (prod aux S) \<le> (\<phi> 1 True) ^ card S"
  assumes "S \<subseteq> insert x (set xs \<union> U)"
  shows "
    measure_pmf.expectation (stp \<bind> cvm xs \<bind> step1 x) (prod aux S) \<le> (\<phi> 1 True) ^ card S"
  sorry

end


context
  fixes q :: real
  fixes h :: "real \<Rightarrow> real"
  assumes "q \<in> {0<..1}"
  assumes "concave_on {0..1/q} h"
  assumes "\<And>x. x \<in> {0..1/q} \<Longrightarrow> h x \<ge> 0"
begin

abbreviation (input)
  \<open>aux2 \<equiv> \<lambda> x state. (
    let p = f ^ (state_k state) in
    of_bool (p > q) * h ((1 / p) * indicat_real (state_chi state) x)
  )\<close>

(* Lemma 3 *)
lemma expectation_cvm':
  assumes U: "finite U"
  assumes "\<And>S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation stp (prod aux2 S) \<le> (h 1) ^ card S"
  assumes "S \<subseteq> set xs \<union> U"
  shows "
    measure_pmf.expectation (stp \<bind> cvm xs) (prod aux2 S) \<le> (h 1) ^ card S"
  sorry

end

end (* end cvm_algo_proof *)

end (* end theory *)
