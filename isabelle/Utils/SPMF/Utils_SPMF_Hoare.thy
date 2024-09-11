theory Utils_SPMF_Hoare

(*
Specialisation of Lean's SatisfiesM to the SPMF monad.
This enables Hoare-logic-like reasoning over (probabilistic) monadic programs.

https://leanprover-community.github.io/mathlib4_docs/Batteries/Classes/SatisfiesM.html

https://cs.ioc.ee/mpc-amast06/amast/mossakowski-slides.pdf 
https://personal.cis.strath.ac.uk/conor.mcbride/Kleisli.pdf
*)

imports
  "CVM.Utils_SPMF_Common"

begin

sledgehammer_params [
  (* verbose = true, *)
  minimize = true,
  preplay_timeout = 15,
  timeout = 60,
  max_facts = smart,
  provers = "
    cvc4 z3 verit
    e vampire spass
  "
]

definition hoare_triple ::
  \<open>['a \<Rightarrow> bool, 'a \<Rightarrow> 'b spmf, 'b \<Rightarrow> bool] \<Rightarrow> bool\<close>
  (\<open>\<turnstile> { _ } _ { _ } \<close> [21, 20, 21] 60) where
  \<open>\<turnstile> { P } f { Q } \<equiv> \<forall> x. P x \<longrightarrow> (AE y in measure_spmf <| f x. Q y)\<close>

abbreviation possibly_evals_to (\<open>\<turnstile> _ \<Down>? _\<close> [20, 2] 60) where
  \<open>\<turnstile> p \<Down>? x \<equiv> x \<in> set_spmf p\<close>

lemma hoare_triple_intro :
  assumes \<open>\<And> x y. \<lbrakk>P x; \<turnstile> f x \<Down>? y\<rbrakk> \<Longrightarrow> Q y\<close>
  shows \<open>\<turnstile> { P } f { Q }\<close>

  by (metis AE_measure_spmf_iff app_def assms hoare_triple_def id_apply) 

lemma hoare_triple_elim :
  fixes x y
  assumes
    \<open>\<turnstile> { P } f { Q }\<close> and
    \<open>P x\<close> and
    \<open>\<turnstile> f x \<Down>? y\<close>
  shows \<open>Q y\<close>

  by (metis AE_measure_spmf_iff app_def assms hoare_triple_def id_apply)

lemma bind_elim :
  assumes \<open>\<turnstile> f x \<bind> g \<Down>? z\<close>
  obtains y where
    \<open>\<turnstile> f x \<Down>? y\<close> and 
    \<open>\<turnstile> g y \<Down>? z\<close>

  using assms by (auto simp add: set_bind_spmf)

lemma precond_postcond :
  assumes
    \<open>\<turnstile> { P } f { Q }\<close> and
    \<open>\<And> x. P' x \<Longrightarrow> P x\<close>
    \<open>\<And> x. Q x \<Longrightarrow> Q' x\<close>
  shows \<open>\<turnstile> { P' } f { Q' }\<close>

  by (metis assms hoare_triple_intro hoare_triple_elim)
  
lemma postcond_true :
  \<open>\<turnstile> { P } f { \<lblot>True\<rblot> }\<close>
  by (simp add: hoare_triple_intro)

lemma fail [simp] :
  \<open>\<turnstile> { P } \<lblot>fail_spmf\<rblot> { Q }\<close>

  by (metis empty_iff hoare_triple_intro set_spmf_return_pmf_None) 

lemma skip [simp] :
  \<open>(\<turnstile> { P } return_spmf { Q }) \<longleftrightarrow> (\<forall> x. P x \<longrightarrow> Q x)\<close>

  by (auto intro!: hoare_triple_intro elim!: hoare_triple_elim)

lemma skip_intro [intro!] :
  assumes \<open>\<And> x. P x \<Longrightarrow> Q x\<close> 
  shows \<open>\<turnstile> { P } return_spmf { Q }\<close>

  using assms by simp

lemma skip_elim [elim!] :
  fixes x
  assumes
    \<open>\<turnstile> { P } return_spmf { Q }\<close> and
    \<open>P x\<close>
  shows \<open>Q x\<close>

  using assms by simp

lemma skip_intro' :
  assumes \<open>\<And> x. P x \<Longrightarrow> Q (f x)\<close>
  shows \<open>\<turnstile> { P } (\<lambda> x. return_spmf (f x)) { Q }\<close>

  by (metis assms hoare_triple_intro set_return_spmf singletonD)

lemma hoare_triple_altdef :
  \<open>\<turnstile> { P } f { Q } \<longleftrightarrow> \<turnstile> { P } f { (\<lambda> y. \<forall> x. P x \<longrightarrow> (\<turnstile> f x \<Down>? y) \<longrightarrow> Q y) }\<close>

  by (smt (verit, ccfv_SIG) hoare_triple_elim hoare_triple_intro) 

lemma seq [intro!] :
  assumes
    \<open>\<turnstile> { P } f { Q }\<close> and
    \<open>\<turnstile> { Q } g { R }\<close>
  shows
    \<open>\<turnstile> { P } f >=> g { R }\<close> and
    \<open>\<turnstile> { P } (\<lambda> x. f x \<bind> g) { R }\<close>

  using assms
  by (auto
      simp add: kleisli_compose_left_def
      intro!: hoare_triple_intro
      elim!: bind_elim hoare_triple_elim)

lemma seq' [intro!] :
  assumes
    \<open>\<turnstile> { P } f { Q }\<close> and
    \<open>\<And> x. P x \<Longrightarrow> \<turnstile> { Q } g x { R }\<close>
  shows
    \<open>\<turnstile> { P } (\<lambda> x. f x \<bind> g x) { R }\<close>

  using assms
  by (smt (verit, best) hoare_triple_elim hoare_triple_intro kleisli_compose_left_def seq(1)) 

lemma if_then_else [intro!] :
  assumes
    \<open>\<And> b. f b \<Longrightarrow> \<turnstile> { P } g { Q }\<close> and
    \<open>\<And> b. \<not> f b \<Longrightarrow> \<turnstile> { P } h { Q }\<close>
  shows
    \<open>\<turnstile> { P } (\<lambda> b. if f b then g b else h b) { Q }\<close>

  using assms
  by (simp add: hoare_triple_def)

lemma loop :
  fixes P :: \<open>'b \<Rightarrow> bool\<close>
  assumes \<open>\<And> x. \<turnstile> { P } f x { P }\<close>
  shows \<open>\<turnstile> { P } foldM_spmf f xs { P }\<close> 

  apply (induction xs) using assms by auto

lemma integral_mono_of_hoare_triple :
  fixes
    x :: 'a and
    f :: \<open>'a \<Rightarrow> 'b spmf\<close> and
    f' g' :: \<open>'b \<Rightarrow> real\<close>
  defines \<open>\<mu> \<equiv> measure_spmf (f x)\<close>
  assumes
    \<open>\<turnstile> { \<lblot>True\<rblot> } f { (\<lambda> y. f' y \<le> g' y) }\<close> and
    \<open>integrable \<mu> f'\<close> and
    \<open>integrable \<mu> g'\<close>
  shows \<open>(\<integral> y. f' y \<partial> \<mu>) \<le> \<integral> y. g' y \<partial> \<mu>\<close>

  using assms by (auto intro!: integral_mono_AE elim!: hoare_triple_elim)

lemma prob_fail_foldM_spmf_le :
  fixes
    p :: real and
    P :: \<open>'b \<Rightarrow> bool\<close>
  assumes
    \<open>p \<ge> 0\<close> and
    \<open>\<And> x. \<turnstile> { P } f x { P }\<close> and
    \<open>\<And> x acc. P acc \<Longrightarrow> prob_fail (f x acc) \<le> p\<close>
  shows \<open>P acc \<Longrightarrow> prob_fail (foldM_spmf f xs acc) \<le> length xs * p\<close>
proof (induction xs arbitrary: acc)
 case Nil
 then show ?case by (simp add: prob_fail_def)
next
  case (Cons x xs)

  let ?acc' = \<open>f x acc\<close>
  let ?\<mu>' = \<open>measure_spmf ?acc'\<close>

  have
    \<open>prob_fail (foldM_spmf f (x # xs) acc)
    = prob_fail ?acc' + \<integral> acc'. prob_fail (foldM_spmf f xs acc') \<partial> ?\<mu>'\<close>
    by (simp add: prob_fail_def pmf_bind_spmf_None)

  also have \<open>... \<le> p + \<integral> acc'. length xs * p \<partial> ?\<mu>'\<close>
  proof -
    have
      \<open>\<turnstile> { \<lblot>True\<rblot> } \<lblot>?acc'\<rblot> { (\<lambda> acc'. prob_fail (foldM_spmf f xs acc') \<le> length xs * p) }\<close>
      using assms Cons.IH \<open>P acc\<close>
      by (smt (verit, ccfv_threshold) hoare_triple_elim hoare_triple_intro skip)

    then have
      \<open>(\<integral> acc'. prob_fail (foldM_spmf f xs acc') \<partial> ?\<mu>') \<le> \<integral> acc'. length xs * p \<partial> ?\<mu>'\<close>
      apply (intro integral_mono_of_hoare_triple[where ?f = \<open>\<lblot>?acc'\<rblot>\<close>])
      using assms foldM_spmf.integrable_prob_fail_foldM_spmf
      by auto

    moreover have \<open>prob_fail ?acc' \<le> p\<close> using \<open>P acc\<close> assms by auto

    ultimately show ?thesis by simp
  qed

  also have \<open>... \<le> p + length xs * p\<close>
  proof -
    have * : \<open>\<And> a b c :: real.
      \<lbrakk>a \<in> {0 .. 1}; b \<ge> 0; c \<ge> 0\<rbrakk> \<Longrightarrow> a * (b * c) \<le> b * c\<close>
      by (simp add: mult_left_le_one_le mult_mono)

    show ?thesis using assms by (auto intro!: * simp add: weight_spmf_le_1)
  qed

  finally show ?case by (simp add: distrib_left mult.commute) 
qed

end