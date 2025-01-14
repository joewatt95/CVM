section \<open>Preliminary Definitions and Lemmas\<close>

theory Negative_Association_Util
  imports
    Concentration_Inequalities.Concentration_Inequalities_Preliminary
begin

(* From Joe Watt *)
abbreviation (input) flip :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'c\<close> where
  \<open>flip f x y \<equiv> f y x\<close>

text \<open>Additional introduction rules for boundedness:\<close>

(* 
  Note to editors: I will move these to (in afp-devel)
  Concentration_Inequalities.Concentration_Inequalities_Preliminary 
*)

lemma bounded_const_min:
  fixes f :: "'a \<Rightarrow> real"
  assumes "bdd_below (f ` M)"
  shows "bounded ((\<lambda>x. min c (f x)) ` M)"
proof -
  obtain h where "\<And>x. x \<in> M \<Longrightarrow> f x \<ge> h" using assms(1) unfolding bdd_below_def by auto
  thus ?thesis by (intro boundedI[where B="max \<bar>c\<bar> \<bar>-h\<bar>"]) force
qed

lemma bounded_prod:
  fixes f :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes "finite I"
  assumes "\<And>i. i \<in> I \<Longrightarrow> bounded (f i ` T)"
  shows "bounded ((\<lambda>x. (\<Prod> i \<in> I. f i x)) ` T)"
  using assms by (induction I) (auto intro:bounded_mult_comp bounded_const)

lemma bounded_vec_mult_comp:
  fixes f g :: "'a \<Rightarrow> real"
  assumes "bounded (f ` T)" "bounded (g ` T)"
  shows "bounded ((\<lambda>x. (f x) *\<^sub>R (g x)) ` T)"
  using bounded_mult_comp[OF assms] by simp

lemma bounded_max:
  fixes f :: "'a \<Rightarrow> real"
  assumes "bounded ((\<lambda>x. f x) ` T)"
  shows "bounded ((\<lambda>x. max c (f x)) ` T)"
proof -
  obtain m where "norm (f x) \<le> m" if "x \<in> T" for x
    using assms unfolding bounded_iff by auto

  thus ?thesis by (intro boundedI[where B="max m c"]) fastforce
qed

lemma bounded_range_imp:
  assumes "bounded (range f)" 
  shows "bounded ((\<lambda>\<omega>. f (h \<omega>)) ` S)"
  by (intro bounded_subset[OF assms]) auto

text \<open>The following allows to state integrability and conditions about the integral simultaneously,
e.g. @{term "has_int_that M f (\<lambda>x. x \<le> c)"} says f is integrable on M and the integral smaller or
equal to @{term "c"}.\<close>

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

text \<open>This is useful to specify which components a functional depends on.\<close>

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

text \<open>There are many results in the field of negative association, where a statement is true
for simultaneously monotone or anti-monotone functions. With the below construction, we introduce
a mechanism where we can parameterize on the direction of a relation:\<close>

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

text \<open>Additional lemmas about clamp for the specific case on reals.\<close>

lemma clamp_eqI2:
  assumes "x \<in> {a..b::real}"
  shows "x = clamp a b x"
  using assms unfolding clamp_def by simp

lemma clamp_eqI:
  assumes "\<bar>x\<bar> \<le> (a::real)"
  shows "x = clamp (-a) a x"
  using assms by (intro clamp_eqI2) auto

lemma clamp_real_def:
  fixes x :: real
  shows "clamp a b x = max a (min x b)"
proof -
  consider (i) "x < a" | (ii) "x \<ge> a" "x \<le> b" | (iii) "x > b" by linarith
  thus ?thesis unfolding clamp_def by (cases) auto
qed

lemma clamp_range:
  assumes "a \<le> b"
  shows "\<And>x. clamp a b x \<ge> a" "\<And>x. clamp a b x \<le> b" "range (clamp a b) \<subseteq> {a..b::real}"
  using assms by (auto simp: clamp_real_def)

lemma clamp_abs_le:
  assumes "a \<ge> (0::real)"
  shows "\<bar>clamp (-a) a x\<bar> \<le> \<bar>x\<bar>"
  using assms unfolding clamp_real_def by simp

lemma bounded_clamp:
  fixes a b :: real
  shows "bounded ((clamp a b \<circ> f) ` S)"
proof (cases "a \<le> b")
  case True
  show ?thesis using clamp_range[OF True] bounded_closed_interval bounded_subset
    by (metis image_comp image_mono subset_UNIV)
next
  case False
  hence "clamp a b (f x) = a" for x unfolding clamp_def by (simp add: max_def)
  hence "(clamp a b \<circ> f) ` S \<subseteq> {a..a}" by auto
  thus ?thesis using bounded_subset bounded_closed_interval by metis
qed

lemma bounded_clamp_alt:
  fixes a b :: real
  shows "bounded ((\<lambda>x. clamp a b (f x)) ` S)"
  using bounded_clamp by (auto simp:comp_def)

lemma clamp_borel[measurable]:
  fixes a b :: "'a::{euclidean_space,second_countable_topology}"
  shows "clamp a b \<in> borel_measurable borel"
  unfolding clamp_def by measurable

lemma monotone_clamp:
  assumes "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) f"
  shows "monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) (\<lambda>\<omega>. clamp a (b::real) (f \<omega>))"
  using assms unfolding monotone_def clamp_real_def by (cases \<eta>) force+  

end