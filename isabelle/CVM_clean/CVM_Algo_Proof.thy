theory CVM_Algo_Proof

imports
  CVM_Algo

begin

locale cvm_algo_proof = cvm_algo +
  assumes f : \<open>1 / 2 \<le> f\<close> \<open>f < 1\<close>
begin                       

(* Copied as-is for Lemma 2 *)
context
  fixes \<phi> :: \<open>real \<Rightarrow> bool \<Rightarrow> real\<close>
  assumes phi : 
    \<open>\<And> x b. \<lbrakk>0 < x; x \<le> 1\<rbrakk> \<Longrightarrow> \<phi> x b \<ge> 0\<close> and
    \<open>\<And> \<alpha> x.
      \<lbrakk>0 < \<alpha>; \<alpha> < 1; 0 < x; x \<le> 1\<rbrakk> \<Longrightarrow>
      (1 - \<alpha>) * \<phi> x False + \<alpha> * \<phi> x True \<le> \<phi> (x / \<alpha>) True \<close> and
    \<open>\<And> x y.
      \<lbrakk>0 < x; x \<le> y; y \<le> 1\<rbrakk> \<Longrightarrow>
      \<phi> x False \<le> \<phi> y False\<close>
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

lemma step_1_preserves_expectation_le :
  assumes
    \<open>finite U\<close>
    \<open>\<And> S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation state (\<Prod> x \<in> S. aux x) \<le> (\<phi> 1 True) ^ card S\<close>
    \<open>S \<subseteq> insert x U\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step_1 x) (\<Prod> x \<in> S. aux x)
    \<le> (\<phi> 1 True) ^ card S\<close>
proof - 
  show ?thesis sorry
qed

lemma step_2_preserves_expectation_le :
  assumes
    \<open>finite U\<close>
    \<open>measure_pmf.expectation state (prod aux S) \<le> (\<phi> 1 True) ^ card S\<close>
    \<open>S \<subseteq> U\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step_2) (\<Prod> x \<in> S. aux x)
    \<le> (\<phi> 1 True) ^ card S\<close>
proof - 
  show ?thesis sorry
qed

lemma step_preserves_expectation_le :
  assumes
    \<open>finite U\<close>
    \<open>\<And> S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation state (\<Prod> x \<in> S. aux x) \<le> (\<phi> 1 True) ^ card S\<close>
    \<open>S \<subseteq> insert x U\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> step x) (\<Prod> x \<in> S. aux x)
    \<le> (\<phi> 1 True) ^ card S\<close>
proof - 
  show ?thesis sorry
qed

lemma expectation_cvm:
  assumes
    \<open>finite U\<close>
    \<open>\<And>S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation state (prod aux S) \<le> (\<phi> 1 True) ^ card S\<close>
  assumes \<open>S \<subseteq> set xs \<union> U\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> run_steps xs) (\<Prod> x \<in> S. aux x)
    \<le> (\<phi> 1 True) ^ card S\<close>
proof - 
  show ?thesis sorry
qed

(* Run some prefix of the elements + one more *)
lemma run_steps_then_step_1_preserves_expectation_le :
  assumes
    \<open>finite U\<close>
    \<open>\<And>S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation state (\<Prod> x \<in> S. aux x) \<le> (\<phi> 1 True) ^ card S\<close>
    \<open>S \<subseteq> insert x (set xs \<union> U)\<close>
  shows
    \<open>measure_pmf.expectation (state \<bind> run_steps xs \<bind> step_1 x) (\<Prod> x \<in> S. aux x)
    \<le> (\<phi> 1 True) ^ card S\<close>
proof -
  show ?thesis sorry
qed

end

context
  fixes q :: real and h :: \<open>real \<Rightarrow> real\<close>
  assumes
    \<open>0 < q\<close> \<open>q \<le> 1\<close> and
    \<open>concave_on {0 .. 1 / q} h\<close> and
    \<open>\<And> x. \<lbrakk>1 \<le> x; x * q \<le> 1\<rbrakk> \<Longrightarrow> h x \<ge> 0\<close>
begin

abbreviation (input)
  \<open>aux' \<equiv> \<lambda> x state. (
    let p = f ^ (state_k state)
    in of_bool (p > q) * h ((1 / p) * indicat_real (state_chi state) x))\<close>

(* Lemma 3 *)
lemma expectation_cvm' :
  assumes U: \<open>finite U\<close>
  assumes \<open>\<And> S.
      S \<subseteq> U \<Longrightarrow>
      measure_pmf.expectation stp (prod aux' S) \<le> (h 1) ^ card S\<close>
  assumes \<open>S \<subseteq> set xs \<union> U\<close>
  shows
    \<open>measure_pmf.expectation (stp \<bind> cvm xs) (prod aux2 S) \<le> (h 1) ^ card S\<close>
proof -
  show ?thesis sorry
qed

end

end (* end cvm_algo_proof *)

end (* end theory *)
