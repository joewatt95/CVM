theory Utils_Hoare_Basic

imports
  "HOL-Library.Monad_Syntax"
  "HOL-Probability.SPMF"
  Utils_Basic

begin

context
  fixes
    bind :: \<open>['a, 'b \<Rightarrow> 'a] \<Rightarrow> 'a\<close> and
    return :: \<open>'b \<Rightarrow> 'a\<close>
  assumes
    monad_laws :
      \<open>bind (return x) f = f x\<close>
      \<open>bind m return = m\<close>
      \<open>bind (bind m f) g = bind m (\<lambda> x. bind (f x) g)\<close>
begin

abbreviation \<open>map' f m \<equiv> bind m (\<lambda> x. return (f x))\<close>

(*
This is inspired by the following similar ideas:
- Lean's "SatisfiesM" predicate
  https://leanprover-community.github.io/mathlib4_docs/Batteries/Classes/SatisfiesM.html

- "Global evaluation formulas" from HasCASL semantics:
  https://www.sciencedirect.com/science/article/pii/S0304397508008670?ref=pdf_download&fr=RR-2&rr=8e805ceaaf9fa3d3 

  Note that this paper also says that one can indeed define a generic notion
  of a monadic while loop in a monad that admits a flat CCPO structure, from
  which the soundness proof follows automatically from transfinite induction
  over the iteration sequence defining the while loop.

Note that `\<And> x. P x \<Longrightarrow> satisfiesM Q (f x)` can then be interpreted as
Hoare triple over Kleisli arrows: `\<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>`.
*)
definition satisfiesM where
  \<open>satisfiesM P m \<equiv> map_spmf P m = map_spmf \<lblot>True\<rblot> m\<close>

(* Experiments showing that satisfiesM characterises total and partial
  correctness for the PMF and SPMF monads respectively. *)

lemma
  \<open>map_pmf P p = map_pmf \<lblot>True\<rblot> p
  \<longleftrightarrow> (AE x in p. P x)\<close>
  by (auto iff: AE_measure_pmf_iff map_pmf_eq_return_pmf_iff)

lemma
  \<open>map_spmf P p = map_spmf \<lblot>True\<rblot> p
  \<longleftrightarrow> (AE x in measure_spmf p. P x)\<close>
  by (smt (verit, best) AE_measure_spmf_iff imageE map_spmf_cong rev_image_eqI set_map_spmf)

lemma skip [simp] :
  \<open>(\<forall> x. P x \<longrightarrow> satisfiesM Q (return_spmf x)) \<longleftrightarrow> (\<forall> x. P x \<longrightarrow> Q x)\<close>
  sorry

end

end