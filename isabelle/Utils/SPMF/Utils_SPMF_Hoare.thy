theory Utils_SPMF_Hoare

(*
Specialisation of Lean's SatisfiesM to the SPMF monad.
This enables Hoare-logic-like reasoning for the partial correctness of spmf
monadic programs.

References:
https://leanprover-community.github.io/mathlib4_docs/Batteries/Classes/SatisfiesM.html
https://link.springer.com/content/pdf/10.1007/3-540-36578-8_19.pdf
https://personal.cis.strath.ac.uk/conor.mcbride/Kleisli.pdf
*)

imports
  Probabilistic_While.While_SPMF
  CVM.Utils_SPMF_FoldM
  CVM.Utils_PMF_Hoare

begin

abbreviation possibly_evals_to
  (\<open>\<turnstile>spmf _ \<Rightarrow>? _\<close> [20, 2] 60) where
  \<open>\<turnstile>spmf p \<Rightarrow>? x \<equiv> x \<in> set_spmf p\<close>

lemma bind_spmfE :
  assumes \<open>\<turnstile>spmf f x \<bind> g \<Rightarrow>? z\<close>
  obtains y where
    \<open>\<turnstile>spmf f x \<Rightarrow>? y\<close>
    \<open>\<turnstile>spmf g y \<Rightarrow>? z\<close>
  using assms by (auto simp add: set_bind_spmf)

definition hoare_triple ::
  \<open>['a \<Rightarrow> bool, 'a \<Rightarrow> 'b spmf, 'b \<Rightarrow> bool] \<Rightarrow> bool\<close>
  (\<open>\<turnstile>spmf \<lbrace> _ \<rbrace> _ \<lbrace> _ \<rbrace> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<equiv> \<forall> x y. P x \<longrightarrow> (\<turnstile>spmf f x \<Rightarrow>? y) \<longrightarrow> Q y\<close>

definition hoare_triple_total ::
  \<open>['a \<Rightarrow> bool, 'a \<Rightarrow> 'b spmf, 'b \<Rightarrow> bool] \<Rightarrow> bool\<close>
  (\<open>\<turnstile>spmf \<lbrakk> _ \<rbrakk> _ \<lbrakk> _ \<rbrakk>\<close> [21, 20, 21] 60) where
  \<open>\<turnstile>spmf \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<equiv> \<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>succeeds_and_satisfies Q\<rbrakk>\<close>

lemma hoare_triple_altdef :
  \<open>(\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>) \<longleftrightarrow> (\<turnstile>pmf \<lbrakk>P\<rbrakk> f \<lbrakk>fails_or_satisfies Q\<rbrakk>)\<close>
  by (simp
    add: hoare_triple_def Utils_PMF_Hoare.hoare_triple_def in_set_spmf
    split: option.splits)

lemma hoare_tripleI :
  assumes \<open>\<And> x y. \<lbrakk>P x; \<turnstile>spmf f x \<Rightarrow>? y\<rbrakk> \<Longrightarrow> Q y\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  by (metis assms hoare_triple_def)

lemma hoare_tripleE :
  assumes
    \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
    \<open>P x\<close>
    \<open>\<turnstile>spmf f x \<Rightarrow>? y\<close>
  shows \<open>Q y\<close>
  by (metis assms hoare_triple_def)

lemma precond_strengthen :
  assumes
    \<open>\<And> x. P x \<Longrightarrow> P' x\<close>
    \<open>\<turnstile>spmf \<lbrace>P'\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  by (metis assms(1,2) hoare_tripleE hoare_tripleI) 

lemma precond_false :
  \<open>\<turnstile>spmf \<lbrace>\<lblot>False\<rblot>\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  by (simp add: hoare_tripleI)

lemma postcond_weaken :
  assumes
    \<open>\<And> x. Q' x \<Longrightarrow> Q x\<close>
    \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q'\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  by (metis assms(1,2) hoare_tripleE hoare_tripleI) 

lemma postcond_true :
  \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>\<lblot>True\<rblot>\<rbrace>\<close>
  by (simp add: hoare_tripleI)

lemma fail [simp] :
  \<open>\<turnstile>spmf \<lbrace>P\<rbrace> \<lblot>fail_spmf\<rblot> \<lbrace>Q\<rbrace>\<close>
  by (metis fail_spmf_def empty_iff hoare_tripleI set_spmf_return_pmf_None)

lemma skip [simp] :
  \<open>(\<turnstile>spmf \<lbrace>P\<rbrace> return_spmf \<lbrace>Q\<rbrace>) \<longleftrightarrow> (\<forall> x. P x \<longrightarrow> Q x)\<close>
  by (auto intro: hoare_tripleI elim: hoare_tripleE)

lemma skip' [simp] :
  \<open>(\<turnstile>spmf \<lbrace>P\<rbrace> (\<lambda> x. return_spmf (f x)) \<lbrace>Q\<rbrace>) \<longleftrightarrow> (\<forall> x. P x \<longrightarrow> Q (f x))\<close>
  by (simp add: hoare_triple_def)

(* lemma hoare_triple_altdef :
  \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<longleftrightarrow> \<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>(\<lambda> y. \<forall> x. P x \<longrightarrow> (\<turnstile>spmf f x \<Rightarrow>? y) \<longrightarrow> Q y)\<rbrace>\<close>
  by (smt (verit, ccfv_SIG) hoare_tripleE hoare_tripleI) *)

lemma if_then_else :
  assumes
    \<open>\<And> x. f x \<Longrightarrow> \<turnstile>spmf \<lbrace>(\<lambda> x'. x = x' \<and> P x)\<rbrace> g \<lbrace>Q\<rbrace>\<close>
    \<open>\<And> x. \<not> f x \<Longrightarrow> \<turnstile>spmf \<lbrace>(\<lambda> x'. x = x' \<and> P x)\<rbrace> h \<lbrace>Q\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> (\<lambda> x. if f x then g x else h x) \<lbrace>Q\<rbrace>\<close>
  using assms by (simp add: hoare_triple_def)

lemma seq :
  assumes
    \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace> \<close>
    \<open>\<turnstile>spmf \<lbrace>Q\<rbrace> g \<lbrace>R\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f >=> g \<lbrace>R\<rbrace>\<close>
  using assms by (auto intro: hoare_tripleI dest: bind_spmfE hoare_tripleE)

lemma seq' :
  assumes
    \<open>\<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
    \<open>\<And> x. P x \<Longrightarrow> \<turnstile>spmf \<lbrace>Q\<rbrace> g x \<lbrace>R\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> (\<lambda> x. (x |> (f >=> g x))) \<lbrace>R\<rbrace>\<close>
  using assms by (smt (verit, ccfv_threshold) hoare_triple_def seq)

context
  fixes
    P :: \<open>nat \<Rightarrow> 'b \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

private abbreviation (input)
  \<open>P' index x val \<equiv>
    (index, x) \<in> set (List.enumerate offset xs) \<and>
    P index val\<close>

lemma loop_enumerate :
  assumes \<open>\<And> index x. \<turnstile>spmf \<lbrace>P' index x\<rbrace> f (index, x) \<lbrace>P (Suc index)\<rbrace>\<close>
  shows \<open>\<turnstile>spmf
    \<lbrace>P offset\<rbrace>
    foldM_spmf_enumerate f xs offset
    \<lbrace>P (offset + length xs)\<rbrace>\<close>
using assms proof (induction xs arbitrary: offset)
  case Nil
  then show ?case by (simp add: foldM_enumerate_def)
next
  case (Cons _ _)
  then show ?case
    apply (simp add: foldM_enumerate_def)
  by (fastforce
    intro!: seq[where Q = \<open>P <| Suc offset\<close>]
    simp add: hoare_triple_def add_Suc[symmetric]
    simp del: add_Suc)
qed

lemma loop :
  assumes \<open>\<And> index x. \<turnstile>spmf \<lbrace>P' index x\<rbrace> f x \<lbrace>P (Suc index)\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P offset\<rbrace> foldM_spmf f xs \<lbrace>P (offset + length xs)\<rbrace>\<close>
  using assms
  by (auto
    intro!: loop_enumerate
    simp add: foldM_eq_foldM_enumerate[where ?offset = offset])

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile>spmf \<lbrace>P\<rbrace> f x \<lbrace>P\<rbrace>\<close>
  shows \<open>\<turnstile>spmf \<lbrace>P\<rbrace> foldM_spmf f xs \<lbrace>P\<rbrace>\<close>
  using loop[where ?P = \<open>curry <| snd >>> P\<close>, where ?offset = 0] assms
  by (fastforce simp add: hoare_triple_def curry_def snd_def)

(*
In general, inductive data types and (partial) recursive functions can be
constructed by standard set theoretic machinery:
1. fixing an appropriate CCPO (the usual approximation ordering for recursive
   functions)
2. fixing an inflationary function (ie endofunctor) that iteratively constructs
   the data type / recursive function and then iterating over the ordinals
3. taking the LFP (ie limit) (at an ordinal \<le> Hartog's number for the sequence)
   so that the inductive definition has the "no-junk" property.

Such a construction affords them induction principles, in that one can induct
over the corresponding inflationary sequence if one wishes to prove a property
holds for some inductive construction.
These include:
- Structural induction (analogous to standard natural number induction) only
  considers finite initial segments of the transfinite sequence, which suffices
  for finitary recursive data types.

- Scott / fixpoint induction, which considers the transfinite sequence up to
  some ordinal bound (\<le> Hartog's number), is useful for
  things like (partial) recursive functions and while loops that may not
  terminate (which form a CPPO under the usual approximation ordering), ie have
  fixed points at or beyond \<omega>.

  Note that:
  - Such a bound exists at \<omega> if the inflationary function is Scott
    continuous, ie preserves limits (ie sups), so that one need only consider
    limits of \<omega>-chains in the limit stages.
  - The Scott induction principle for while loops essentially yields the
    soundness of the (partial) Hoare rule for while loops,

For details, see for instance:
https://pcousot.github.io/publications/Cousot-LOPSTR-2019.pdf

Note that partial recursive functions in Isabelle are defined as above, via the
`partial_function` command from the `HOL.Partial_Function` package.
The Scott induction `partial_function_definitions.fixp_induct_uc` rule there
comes directly from `ccpo.fixp_induct`, which in turn arises from transfinite
induction over the transfinite iteration sequence `ccpo.iterates` of an
inflationary / monotone function.
Note that here, Scott-continuity is not enforced, only monotonicity.

Consequently, the probabilistic while loop combinator `loop_spmf.while`, defined
as a partial recursive function via `partial_function`, admits a Scott induction
principle `loop_spmf.while_fixp_induct` with 3 cases, each corresponding to each
case of a transfinite induction argument, namely:
- `adm` aka CCPO admissibility, handles limit ordinals.
- `bottom` handles the base case, with `\<bottom> = return_pmf None`
- `step` handles successor ordinals.

Note that in general, endofunctors over spmf need not be Scott continuous
(see pg 560 of https://ethz.ch/content/dam/ethz/special-interest/infk/inst-infsec/information-security-group-dam/research/publications/pub2020/Basin2020_Article_CryptHOLGame-BasedProofsInHigh.pdf )
so that fixpoints may only be found beyond \<omega>, which means that one may not be
able to consider only \<omega>-chains for the `adm` step.
*)

(* thm partial_function_definitions.fixp_induct_uc
thm ccpo.fixp_induct
term ccpo.iterates
thm ccpo_spmf *)

(*
Admissibility of Hoare triple, ie sups of chains of Kleisli arrows f satisfying
a (partial correctness) Hoare triple also satsify it.

This is useful when one wants to use a transfinite iteration / Zorn's Lemma
argument, like when inducting on the transfinite iteration of the endofunctor
defining probabilistic while loops to show that a Hoare triple continues to hold
after the while loop.

Note that one can interpret the notion of a while loop / Y combinator as the
limit of the usual transfinite iteration sequence in monads with a flat CCPO
structure (including the identity monad).
Consequently, this notion of a while loop, along with the proofs of
admissibility of Hoare triples and (partial correctness) Hoare while rule can
be copy pasted to all other such monads.
*)
lemma admissible_hoare_triple :
  \<open>spmf.admissible <| \<lambda> f. \<turnstile>spmf \<lbrace>P\<rbrace> f \<lbrace>Q\<rbrace>\<close>
  by (simp add: hoare_triple_def)

lemma while :
  assumes \<open>\<And> x. guard x \<Longrightarrow> \<turnstile>spmf \<lbrace>(\<lambda> x'. x = x' \<and> P x)\<rbrace> body \<lbrace>P\<rbrace>\<close>
  defines
    [simp] :
      \<open>while_triple postcond \<equiv>
        \<turnstile>spmf \<lbrace>P\<rbrace> loop_spmf.while guard body \<lbrace>postcond\<rbrace>\<close>
  shows
    \<open>while_triple (\<lambda> x. \<not> guard x \<and> P x)\<close> (is ?thesis_0) 
    \<open>while_triple P\<close> (is ?thesis_1)
proof -
  show ?thesis_0
    apply simp
    apply (induction rule: loop_spmf.while_fixp_induct)
    using assms
    by (auto
      intro!: admissible_hoare_triple fail if_then_else seq'
      simp add: fail_spmf_def[symmetric])

  then show ?thesis_1
    by (simp, metis (mono_tags, lifting) Utils_SPMF_Hoare.postcond_weaken)
qed

lemma integral_mono_of_hoare_triple :
  fixes
    x :: 'a and
    f :: \<open>'a \<Rightarrow> 'b spmf\<close> and
    g h :: \<open>'b \<Rightarrow> real\<close>
  defines \<open>\<mu> \<equiv> measure_spmf (f x)\<close>
  assumes
    \<open>\<turnstile>spmf \<lbrace>\<lblot>True\<rblot>\<rbrace> f \<lbrace>(\<lambda> y. g y \<le> h y)\<rbrace>\<close>
    \<open>integrable \<mu> g\<close>
    \<open>integrable \<mu> h\<close>
  shows \<open>(\<integral> y. g y \<partial> \<mu>) \<le> \<integral> y. h y \<partial> \<mu>\<close>
  using assms by (auto intro!: integral_mono_AE elim!: hoare_tripleE)

lemma prob_fail_foldM_spmf_le :
  fixes
    p :: real and
    P :: \<open>'b \<Rightarrow> bool\<close>
  assumes
    \<open>\<And> x. \<turnstile>spmf \<lbrace>P\<rbrace> f x \<lbrace>P\<rbrace>\<close>
    \<open>\<And> x val. P val \<Longrightarrow> prob_fail (f x val) \<le> p\<close>
    \<open>P val\<close>
  shows \<open>prob_fail (foldM_spmf f xs val) \<le> length xs * p\<close>
using assms proof (induction xs arbitrary: val)
  case Nil
  then show ?case by (simp add: prob_fail_def)
next
  case (Cons x xs)

  let ?val' = \<open>f x val\<close>
  let ?\<mu>' = \<open>measure_spmf ?val'\<close>

  have
    \<open>prob_fail (foldM_spmf f (x # xs) val) =
      prob_fail ?val' + \<integral> val'. prob_fail (foldM_spmf f xs val') \<partial> ?\<mu>'\<close>
    (is \<open>_ = _ + \<integral> val'. ?prob_fail val' \<partial> _\<close>)
    by (simp add: prob_fail_def pmf_bind_spmf_None)

  also have \<open>\<dots> \<le> p + \<integral> _. length xs * p \<partial> ?\<mu>'\<close>
  proof -
    from Cons.IH assms \<open>P val\<close>
    have \<open>\<turnstile>spmf \<lbrace>\<lblot>True\<rblot>\<rbrace> \<lblot>?val'\<rblot> \<lbrace>(\<lambda> val'. ?prob_fail val' \<le> length xs * p)\<rbrace>\<close>
      by (simp add: Utils_SPMF_Hoare.hoare_triple_def)

    then have \<open>(\<integral> val'. ?prob_fail val' \<partial> ?\<mu>') \<le> \<integral> _. length xs * p \<partial> ?\<mu>'\<close>
      apply (intro integral_mono_of_hoare_triple[where f = \<open>\<lblot>?val'\<rblot>\<close>])
      by (simp_all add: integrable_prob_fail_foldM_spmf)

    with \<open>P val\<close> assms(2) show ?thesis by (simp add: add_mono)
  qed

  also have \<open>\<dots> \<le> p + length xs * p\<close>
    apply simp
    by (metis assms(2) local.Cons(4) measure_spmf.subprob_measure_le_1 mult.commute mult_left_le mult_nonneg_nonneg of_nat_0_le_iff order_trans pmf_nonneg prob_fail_def)

  finally show ?case by (simp add: algebra_simps)
qed

end