theory Negative_Association_Util
  imports "HOL-Probability.Probability"
begin


lemma bounded_const_min:
  fixes f :: "'a \<Rightarrow> real"
  assumes "bdd_below (f ` M)"
  shows "bounded ((\<lambda>x. min c (f x)) ` M)"
proof -
  obtain h where "\<And>x. x \<in> M \<Longrightarrow> f x \<ge> h" using assms(1) unfolding bdd_below_def by auto
  thus ?thesis by (intro boundedI[where B="max \<bar>c\<bar> \<bar>-h\<bar>"]) force 
qed

definition has_int_that where 
  "has_int_that M f P = (integrable M f \<and> (P (\<integral>\<omega>. f \<omega> \<partial>M)))"

lemma true_eq_iff: "P \<Longrightarrow> True = P" by auto
lemma le_trans: "y \<le> z \<Longrightarrow> x \<le> y \<longrightarrow> x \<le> (z :: 'a :: order)" by auto

lemma has_int_that_mono:
  assumes "\<And>x. P x \<longrightarrow> Q x"
  shows "has_int_that M f P \<le> has_int_that M f Q"
  using assms unfolding has_int_that_def by auto

lemma has_int_thatD:
  assumes "has_int_that M f P"
  shows "integrable M f" "P (integral\<^sup>L M f)"
  using assms has_int_that_def by auto


definition depends_on :: "(('a \<Rightarrow> 'b) \<Rightarrow> 'c) \<Rightarrow> 'a set \<Rightarrow> bool"
  where "depends_on f I = (\<forall>x y. restrict x I = restrict y I \<longrightarrow> f x = f y)"

lemma depends_onI:
  assumes "\<And>x.  f x = f (\<lambda>i. if i \<in> I then (x i) else undefined)"
  shows "depends_on f I"
proof -
  have "f x = f y" if "restrict x I = restrict y I" for x y
  proof -
    have "f x = f (restrict x I)" using assms unfolding restrict_def by simp
    also have "... = f (restrict y I)" using that by simp
    also have "... = f y" using assms unfolding restrict_def by simp
    finally show ?thesis by simp
  qed
  thus ?thesis unfolding depends_on_def by blast
qed

lemma depends_on_comp: 
  assumes "depends_on f I"
  shows "depends_on (g \<circ> f) I"
  using assms unfolding depends_on_def by (metis o_apply)

lemma depends_on_comp_2:
  assumes "depends_on f I"
  shows "depends_on (\<lambda>x. g (f x)) I"
  using assms unfolding depends_on_def by metis

lemma depends_onD:
  assumes "depends_on f I"
  shows "f \<omega> = f (\<lambda>i\<in>I. (\<omega> i))"
  using assms unfolding depends_on_def by (metis extensional_restrict restrict_extensional)

lemma depends_onD2:
  assumes "depends_on f I" "restrict x I = restrict y I"
  shows "f x = f y"
  using assms unfolding depends_on_def by metis

lemma depends_on_empty:
  assumes "depends_on f {}"
  shows "f \<omega> = f undefined" 
  by (intro depends_onD2[OF assms]) auto

lemma depends_on_mono:
  assumes "I \<subseteq> J" "depends_on f I"
  shows "depends_on f J"
  using assms unfolding depends_on_def by (metis restrict_restrict Int_absorb1)

abbreviation "square_integrable M f \<equiv> integrable M ((power2 :: real \<Rightarrow> real) \<circ> f)"

(* 
  The following allows us to state theorems with multiple monotonicity variants.
*)

datatype RelDirection = Fwd | Rev

definition dir_le :: "RelDirection \<Rightarrow> (('d::order) \<Rightarrow> ('d :: order) \<Rightarrow> bool)"  (infixl "\<le>\<ge>\<index>" 60)
  where "dir_le \<eta> = (if \<eta> = Fwd then (\<le>) else (\<ge>))"

lemma dir_le[simp]: 
  "(\<le>\<ge>\<^bsub>Fwd\<^esub>) = (\<le>)" 
  "(\<le>\<ge>\<^bsub>Rev\<^esub>) = (\<ge>)" 
  by (auto simp:dir_le_def)

definition dir_sign :: "RelDirection \<Rightarrow> 'a::{one,uminus}" ("\<plusminus>\<index>")
  where "dir_sign \<eta> = (if \<eta> = Fwd then 1 else (-1))"

lemma dir_sign[simp]: 
  "(\<plusminus>\<^bsub>Fwd\<^esub>) = (1)" 
  "(\<plusminus>\<^bsub>Rev\<^esub>) = (-1)" 
  by (auto simp:dir_sign_def)

lemma conv_rel_to_sign:
  fixes f :: "'a::order \<Rightarrow> real"
  shows "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) f = mono ((*)(\<plusminus>\<^bsub>\<eta>\<^esub>) \<circ> f)" 
  by (cases "\<eta>") (simp_all add:monotone_def)

instantiation RelDirection :: times
begin
definition times_RelDirection :: "RelDirection \<Rightarrow> RelDirection \<Rightarrow> RelDirection" where 
  times_RelDirection_def: "times_RelDirection x y = (if x = y then Fwd else Rev)"

instance by standard
end

lemmas rel_dir_mult[simp] = times_RelDirection_def

lemma dir_mult_hom: "(\<plusminus>\<^bsub>\<sigma> * \<tau>\<^esub>) = (\<plusminus>\<^bsub>\<sigma>\<^esub>) * ((\<plusminus>\<^bsub>\<tau>\<^esub>)::real)"
  unfolding dir_sign_def times_RelDirection_def by (cases \<sigma>,auto intro:RelDirection.exhaust) 

end