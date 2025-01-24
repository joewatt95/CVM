section \<open>Abstract Algorithm\label{sec:cvm_abs}\<close>

text \<open>This section verifies an abstract version of the CVM algorithm, where the subsampling step
can be an arbitrary randomized algorithm, fulfilling an expectation invariant.

It is presented in Algorithm~\ref{alg:cvm_abs}.

\begin{algorithm}[h!]
	\caption{Abstract CVM algorithm.\label{alg:cvm_abs}}
	\begin{algorithmic}[1]       
  \Require Stream elements $a_1,\ldots,a_l$, $0 < \varepsilon$, $0 < \delta < 1$, $f$ subsampling param.
  \Ensure An estimate $R$, s.t., $\prob \left( | R - |A| | > \varepsilon |A| \right) \leq \delta$ where $A := \{a_1,\ldots,a_l\}.$
  \State $\chi \gets \{\}, p \gets 1, n \geq \left\lceil \frac{12}{\varepsilon^2} \ln(\frac{3l}{\delta}) \right\rceil$
  \For{$i \gets 1$ to $l$}
    \State $b \getsr \Ber(p)$ \Comment insert $a_i$ with probability $p$ (and remove it otherwise)
    \If{$b$}
      \State $\chi \gets \chi \cup \{a_i\}$
    \Else
      \State $\chi \gets \chi - \{a_i\}$
    \EndIf
    \If{$|\chi| = n$}
      \State $\chi \getsr \mathrm{subsample}(\chi)$ \Comment abstract subsampling step
      \State $p \gets p f$
    \EndIf
  \EndFor
  \State \Return $\frac{|\chi|}{p}$ \Comment estimate cardinality of $A$
\end{algorithmic}        
\end{algorithm}

For the subsampling step we assume that it fulfills the following inequality:
                                        
\begin{equation}
\label{eq:subsample_condition}     
\int_{\mathrm{subsample}(\chi)} \left(\prod_{i \in S} g(i \in \omega) d \omega\right) \leq 
  \prod_{i \in S} \left(\int_{Ber(f)} g(\omega) \omega\right)      
\end{equation}
for all non-negative functions $g$ and $S \subseteq \chi$. 

Note that, $\mathrm{Ber}(p)$ denotes the Bernoulli-distribution.
                                                      
The original CVM algorithm uses a subsampling step, where each element is retained with probability
$f$. It is straight-forward to see that this fulfills the above condition.

The new CVM algorithm proposed in this work, uses a subsampling step, where a random $nf$-subset
of the elements are kept. This also fulfills the above inequality, although this is harder to
prove and will be explained in more detail in Section~\ref{sec:cvm_new}.

In this section, we'll verify that the above algorithm indeed fulfills the desired conditions, as
well as, unbiasedness, i.e., that: $\expect [R] = |A|$.
The part that is not going to be verified in this section, is the fact that the algorithm keeps at
most $n$ elements in the state $\chi$, because it is not unconditionally true, but will be ensured
(by different means) for the concrete instantiations in the following sections.\<close>

theory CVM_Abstract_Algorithm

imports
  Probabilistic_Prime_Tests.Generalized_Primality_Test
  "HOL-Decision_Procs.Approximation"
  CVM_Subsample.Utils_PMF
  Finite_Fields.Finite_Fields_More_PMF
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
begin

unbundle no_vec_syntax

record 'a state =
  state_k :: nat
  state_\<chi> :: \<open>'a set\<close>

lemma bounded_finite:
  assumes \<open>finite S\<close>
  shows \<open>bounded (f ` S)\<close>
  using assms by (intro finite_imp_bounded) auto

lemma of_bool_power:
  assumes \<open>y > 0\<close>
  shows \<open>(of_bool x::real) ^ (y::nat) = of_bool x\<close>
  by (simp add: assms)

datatype 'a run_state = FinalState \<open>'a list\<close> | IntermState \<open>'a list\<close> \<open>'a\<close>

lemma run_state_induct:
  assumes \<open>P (FinalState [])\<close>
  assumes \<open>\<And>xs x. P (FinalState xs) \<Longrightarrow> P (IntermState xs x)\<close>
  assumes \<open>\<And>xs x. P (IntermState xs x) \<Longrightarrow> P (FinalState (xs@[x]))\<close>
  shows \<open>P result\<close>
proof -
  have \<open>P (FinalState xs) \<and> P (IntermState xs x)\<close> for xs x
    using assms by (induction xs rule:rev_induct) auto
  thus ?thesis by (cases result) auto
qed

locale cvm_algo_abstract =
  fixes thresh :: nat and f :: real and subsample :: \<open>'a set \<Rightarrow> 'a set pmf\<close>
  assumes thresh_gt_0: \<open>thresh > 0\<close>
  assumes f_range: \<open>f \<in> {1/2..<1}\<close>
  assumes subsample:
    \<open>\<And>U x. card U = thresh \<Longrightarrow> x \<in> set_pmf (subsample U) \<Longrightarrow> x \<subseteq> U\<close>
  assumes subsample_inequality:
    \<open>\<And>g U S. S \<subseteq> U 
      \<Longrightarrow> card U = thresh
      \<Longrightarrow> range g \<subseteq> {0::real..}
      \<Longrightarrow> (\<integral>\<omega>. (\<Prod>s\<in>S. g(s \<in> \<omega>)) \<partial>subsample U) \<le> (\<Prod>s\<in>S. (\<integral>\<omega>. g \<omega> \<partial>bernoulli_pmf f))\<close>    
begin

text \<open>Line 1:\<close>
definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> \<lparr>state_k = 0, state_\<chi> = {}\<rparr>\<close>

text \<open>Lines 3-7:\<close>
definition step_1 :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_1 x \<sigma> =
    do {
      let k = state_k \<sigma>;
      let \<chi> = state_\<chi> \<sigma>; 
  
      insert_x_into_\<chi> \<leftarrow> bernoulli_pmf (f ^ k);
  
      let \<chi> = (
        if insert_x_into_\<chi>
        then insert x \<chi>
        else Set.remove x \<chi>
      );
  
      return_pmf (\<sigma>\<lparr>state_\<chi> := \<chi>\<rparr>)
    }\<close>

text \<open>Lines 8-10:\<close>
definition step_2 :: \<open>'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_2 \<sigma> = do {
    let k = state_k \<sigma>;
    let \<chi> = state_\<chi> \<sigma>;

    if card \<chi> = thresh
    then do {
      \<chi> \<leftarrow> subsample \<chi>;
      return_pmf \<lparr>state_k = k + 1, state_\<chi> = \<chi>\<rparr>
    } else
      return_pmf \<sigma> 
    }\<close>

text \<open>Lines 1-10:\<close>
definition run_steps :: \<open>'a list \<Rightarrow> 'a state pmf\<close> where
  \<open>run_steps xs \<equiv> foldM_pmf (\<lambda>x \<sigma>. step_1 x \<sigma> \<bind> step_2) xs initial_state\<close>

text \<open>Line 11:\<close>
definition estimate :: \<open>'a state \<Rightarrow> real\<close> where
  \<open>estimate \<sigma> = card (state_\<chi> \<sigma>) / f^state_k \<sigma>\<close>

definition \<open>state_p \<sigma> = f ^ state_k \<sigma>\<close>

lemma run_steps_snoc: \<open>run_steps (xs @[x]) = run_steps xs \<bind> step_1 x \<bind> step_2\<close>
  unfolding run_steps_def foldM_pmf_snoc by (simp add:bind_assoc_pmf)

fun run_state_pmf where
  \<open>run_state_pmf (FinalState xs) = run_steps xs\<close> |
  \<open>run_state_pmf (IntermState xs x) = run_steps xs \<bind> step_1 x\<close>

fun len_run_state where
  \<open>len_run_state (FinalState xs) = length xs\<close> |
  \<open>len_run_state (IntermState xs x) = length xs\<close>

fun run_state_set where
  \<open>run_state_set (FinalState xs) = set xs\<close> |
  \<open>run_state_set (IntermState xs x) = set xs \<union> {x}\<close>

lemma finite_run_state_set[simp]: \<open>finite (run_state_set \<sigma>)\<close> by (cases \<sigma>) auto

lemma subsample_finite_pmf: 
  assumes \<open>card U = thresh\<close>
  shows \<open>finite (set_pmf (subsample U))\<close>
proof-
  have \<open>finite (Pow U)\<close> unfolding finite_Pow_iff using assms thresh_gt_0 card_gt_0_iff by blast
  from finite_subset[OF _ this] show ?thesis using subsample[OF assms] by auto
qed

lemma step_2_preserves_finite_support :
  assumes \<open>finite (set_pmf \<sigma>)\<close>
  shows \<open>finite (set_pmf (\<sigma> \<bind> step_2))\<close>
  using assms subsample_finite_pmf by (auto simp:step_2_def Let_def)

lemma finite_run_state_pmf: \<open>finite (set_pmf (run_state_pmf \<rho>))\<close>
proof (induction \<rho> rule:run_state_induct)
  case 1 thus ?case by (simp add:run_steps_def)
next
  case (2 xs x) thus ?case by (simp add:step_1_def Let_def)
next
  case (3 xs x)
  have a: \<open>run_state_pmf (FinalState (xs@[x])) = run_state_pmf (IntermState xs x) \<bind> step_2\<close>
    by (simp add:run_steps_snoc)
  show ?case unfolding a using step_2_preserves_finite_support[OF 3] by simp
qed

lemma state_\<chi>_run_state_pmf:
  \<open>AE \<omega> in run_state_pmf \<rho>. state_\<chi> \<omega> \<subseteq> run_state_set \<rho>\<close>
proof (induction \<rho> rule:run_state_induct)
  case 1 thus ?case by (simp add:run_steps_def AE_measure_pmf_iff initial_state_def)
next
  case (2 xs x)
  then show ?case by (simp add:AE_measure_pmf_iff Let_def step_1_def remove_def) auto
next
  case (3 xs x)
  let ?p = \<open>run_state_pmf (IntermState xs x)\<close>
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = ?p \<bind> step_2\<close>
    by (simp add:run_steps_snoc)
  thus ?case unfolding b using subsample 3 by (simp add:AE_measure_pmf_iff step_2_def Let_def) blast
qed

text \<open>Lemma~\ref{le:neg_cor_prelim}:\<close>
lemma run_steps_preserves_expectation_le:
  fixes \<phi> :: \<open>real \<Rightarrow> bool \<Rightarrow> real\<close>
  assumes phi :
    \<open>\<And> x b. \<lbrakk>0 < x; x \<le> 1\<rbrakk> \<Longrightarrow> \<phi> x b \<ge> 0\<close>
    \<open>\<And> p x. \<lbrakk>0 < p; p \<le> 1; 0 < x; x \<le> 1\<rbrakk> \<Longrightarrow> (\<integral>\<omega>. \<phi> x \<omega> \<partial>bernoulli_pmf p) \<le> \<phi> (x / p) True\<close>
    \<open>mono_on {0..1} (\<lambda>x. \<phi> x False)\<close>
  defines \<open>aux \<equiv> \<lambda> S \<sigma>. (\<Prod> x \<in> S. \<phi> (f ^ state_k \<sigma>) (x \<in> state_\<chi> \<sigma>))\<close>
  assumes \<open>S \<subseteq> run_state_set \<rho>\<close>
  shows \<open>measure_pmf.expectation (run_state_pmf \<rho>) (aux S) \<le> \<phi> 1 True ^ card S\<close>
  using assms(5)
proof (induction \<rho> arbitrary: S rule: run_state_induct)
  case 1 thus ?case by (simp add:aux_def)
next
  case (2 xs x)

  have \<open>finite (set_pmf (run_steps xs))\<close>
    using finite_run_state_pmf[where \<rho>=\<open>FinalState xs\<close>] by simp
  note [simp] = integrable_measure_pmf_finite[OF this]

  have fin_S: \<open>finite S\<close> using finite_run_state_set 2(2) finite_subset by auto

  have b: \<open>aux S \<omega> = aux (S - {x}) \<omega> * aux (S \<inter> {x}) \<omega>\<close> for \<omega> :: \<open>'a state\<close>
    unfolding aux_def using fin_S by (subst prod.union_disjoint[symmetric]) (auto intro:prod.cong)

  have c: \<open>finite (set_pmf (run_steps xs \<bind> step_1 x))\<close>
    using finite_run_state_pmf[where \<rho>=\<open>IntermState xs x\<close>] by simp

  have d:\<open>(\<integral>u. aux (S\<inter>{x}) u \<partial>step_1 x \<tau>) \<le> \<phi> 1 True^(card (S \<inter> {x}))\<close>  (is \<open>?L \<le> ?R\<close>)
    if \<open>\<tau> \<in> set_pmf (run_steps xs)\<close> for \<tau> 
  proof(cases \<open>x \<in> S\<close>)
    case True
    hence \<open>?L = measure_pmf.expectation (bernoulli_pmf (f ^ state_k \<tau>)) (\<lambda>x. \<phi> (f ^ state_k \<tau>) x)\<close>
      unfolding step_1_def Let_def map_pmf_def[symmetric] integral_map_pmf aux_def
      by (intro integral_cong_AE AE_pmfI) simp_all
    also have \<open>\<dots> \<le> \<phi> (f ^ state_k \<tau> / f ^ state_k \<tau>) True\<close>
      using f_range by (intro phi(2) power_le_one zero_less_power) auto
    also have \<open>\<dots> \<le> \<phi> 1 True\<close> using f_range by (simp add:divide_simps)
    also have \<open>\<dots> = \<phi> 1 True ^ card (S \<inter> {x})\<close> using True by simp
    finally show ?thesis by simp
  next 
    case False thus ?thesis by (simp add:aux_def)
  qed

  have e: \<open>aux (S-{x}) \<tau> \<ge> 0\<close> for \<tau>
    using f_range unfolding aux_def by (intro prod_nonneg phi(1) power_le_one) auto

  have \<open>(\<integral>\<tau>. aux S \<tau> \<partial>(bind_pmf (run_steps xs) (step_1 x))) = 
    (\<integral>\<tau>. (\<integral>u. aux (S - {x}) \<tau> * aux (S \<inter> {x}) u \<partial>step_1 x \<tau>) \<partial>run_steps xs)\<close>
    unfolding integral_bind_pmf[OF bounded_finite[OF c]] b
    by (intro integral_cong_AE AE_pmfI arg_cong2[where f=\<open>(*)\<close>] prod.cong) 
      (auto simp:step_1_def aux_def Let_def) 
  also have \<open>\<dots> = (\<integral>\<tau>. aux (S-{x}) \<tau> * (\<integral>u. aux (S\<inter>{x}) u \<partial>step_1 x \<tau>) \<partial>run_steps xs)\<close>
    by simp
  also have \<open>\<dots> \<le> (\<integral>\<tau>. aux (S-{x}) \<tau> * (\<phi> 1 True)^ card (S\<inter>{x}) \<partial>run_steps xs)\<close>
    by (intro integral_mono_AE AE_pmfI mult_left_mono d e) auto
  also have \<open>\<dots> = (\<phi> 1 True) ^ card (S\<inter>{x}) * (\<integral>\<tau>. aux (S-{x}) \<tau> \<partial>(run_state_pmf (FinalState xs)))\<close>
    by simp
  also have \<open>\<dots> \<le> (\<phi> 1 True) ^ card (S\<inter>{x}) * (\<phi> 1 True)^ card (S - {x})\<close>
    using phi(1) 2(2) by (intro mult_left_mono 2(1)) auto
  also have \<open>\<dots> = (\<phi> 1 True) ^ (card ((S\<inter>{x}) \<union> (S-{x})))\<close>
    using fin_S by (subst card_Un_disjoint) (auto simp add:power_add)
  also have \<open>\<dots> = (\<phi> 1 True) ^ card S\<close> by (auto intro!:arg_cong2[where f=\<open>\<lambda>x y. x ^ (card y)\<close>])
  finally show ?case by simp 
next
  case (3 xs x)
  define p where  \<open>p = run_state_pmf (IntermState xs x)\<close>
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = p \<bind> step_2\<close>
    by (simp add:run_steps_snoc p_def)

  have fin_S: \<open>finite S\<close> using finite_run_state_set 3(2) finite_subset by auto

  have \<open>finite (set_pmf p)\<close>
    using finite_run_state_pmf[where \<rho>=\<open>IntermState xs x\<close>] by (simp add:p_def)
  note [simp] = integrable_measure_pmf_finite[OF this]

  have q:\<open>finite (set_pmf (p \<bind> step_2))\<close>
    using finite_run_state_pmf[where \<rho>=\<open>FinalState (xs@[x])\<close>] b by simp

  have c: \<open>(\<integral>u. (\<Prod>s\<in>S. \<phi> (f * f ^ state_k \<tau>) (s \<in> u)) \<partial>subsample (state_\<chi> \<tau>)) \<le> aux S \<tau>\<close>
    (is \<open>?L \<le> ?R\<close>) if that': \<open>\<tau> \<in> set_pmf p\<close> \<open>card(state_\<chi> \<tau>) = thresh\<close> for \<tau>
  proof -
    let ?q = \<open>subsample (state_\<chi> \<tau>)\<close>
    let ?U = \<open>state_\<chi> \<tau>\<close>

    define k' where \<open>k' = state_k \<tau>+1\<close>
    note d = that
    hence e:\<open>finite (state_\<chi> \<tau>)\<close> using thresh_gt_0 card_gt_0_iff by blast 

    have g: \<open>y \<subseteq> state_\<chi> \<tau>\<close> if \<open>y \<in> set_pmf (subsample (state_\<chi> \<tau>))\<close> for y 
      using subsample[OF that'(2)] that by auto

    have h: \<open>f ^ k' \<in> {0<..1}\<close> using f_range by (auto intro:power_le_one)
    have h2: \<open>f ^ state_k \<tau> \<in> {0<..1}\<close> using f_range by (auto intro:power_le_one)

    have \<open>?L = (\<integral>u. (\<Prod>s\<in>(S-?U) \<union> (S\<inter>?U). \<phi> (f^k') (s\<in>u)) \<partial>?q)\<close>
      unfolding k'_def using fin_S by (intro integral_cong_AE prod.cong AE_pmfI) auto 
    also have \<open>\<dots> = (\<integral>u. (\<Prod>s\<in>S-?U. \<phi> (f^k') (s\<in>u)) * (\<Prod>s\<in>(S\<inter>?U). \<phi> (f^k') (s\<in>u)) \<partial>?q)\<close>
      using fin_S by (subst prod.union_disjoint) auto
    also have \<open>\<dots> = (\<integral>u. (\<Prod>s\<in>S-?U. \<phi> (f^k') False) * (\<Prod>s\<in>(S\<inter>?U). \<phi>(f^k') (s\<in>u)) \<partial>?q)\<close>
      using g by (intro integral_cong_AE AE_pmfI arg_cong2[where f=\<open>(*)\<close>] prod.cong 
          arg_cong2[where f=\<open>\<phi>\<close>]) auto
    also have \<open>\<dots> = (\<Prod>s\<in>S-?U. \<phi> (f^k') False) * (\<integral>u. (\<Prod>s\<in>S\<inter>?U. \<phi> (f^k') (s\<in>u)) \<partial>?q)\<close>
      by simp
    also have \<open>\<dots> \<le> (\<Prod>s\<in>S-?U. \<phi> (f^k') False) * (\<Prod>s\<in>S\<inter>?U. (\<integral>u. \<phi> (f^k') u \<partial>bernoulli_pmf f))\<close>
      using d h by (intro mult_left_mono subsample_inequality prod_nonneg) (auto intro!:phi(1))
    also have \<open>\<dots> \<le> (\<Prod>s\<in>S-?U. \<phi> (f^k') False) * (\<Prod>s\<in>S\<inter>?U. \<phi> (f^k'/f) True)\<close>
      using h f_range 
      by (intro mult_left_mono prod_mono phi(2) conjI integral_nonneg_AE AE_pmfI phi(1) prod_nonneg)
         auto
    also have \<open>\<dots> \<le> (\<Prod>s\<in>S-?U. \<phi> (f^state_k \<tau>) False) * (\<Prod>s\<in>S\<inter>?U. \<phi> (f^state_k \<tau>) True)\<close>
      using h h2 f_range unfolding k'_def
      by (intro mult_mono prod_mono conjI phi(1) mono_onD[OF phi(3)] prod_nonneg power_le_one) auto
    also have \<open>\<dots> = (\<Prod>s\<in>S-?U. \<phi>(f^state_k \<tau>) (s \<in> ?U)) * (\<Prod>s\<in>S\<inter>?U. \<phi>(f^state_k \<tau>) (s \<in> ?U))\<close>
      by simp
    also have \<open>\<dots> = (\<Prod>s\<in>(S-?U)\<union>(S\<inter>?U). \<phi>(f^state_k \<tau>) (s \<in> ?U))\<close>
      using fin_S by (subst prod.union_disjoint[symmetric]) (auto)
    also have \<open>\<dots> = aux S \<tau>\<close> unfolding aux_def by (intro prod.cong) auto
    finally show ?thesis by simp
  qed

  have \<open>(\<integral>\<tau>. aux S \<tau> \<partial>run_state_pmf (FinalState (xs@[x]))) = (\<integral>\<tau>. aux S \<tau> \<partial>bind_pmf p step_2)\<close>
    unfolding b by simp
  also have \<open>\<dots> = (\<integral>\<tau>. (\<integral>u. aux S u \<partial>step_2 \<tau>) \<partial>p)\<close> by (intro integral_bind_pmf bounded_finite q)
  also have \<open>\<dots> = (\<integral>\<tau>. (if card(state_\<chi> \<tau>) = thresh then 
    (\<integral>u. (\<Prod>s\<in>S. \<phi> (f * f ^ state_k \<tau>) (s \<in> u)) \<partial>subsample (state_\<chi> \<tau>)) else aux S \<tau>) \<partial>p)\<close>
    unfolding step_2_def map_pmf_def[symmetric] Let_def aux_def 
    by (simp add:if_distrib if_distribR cong:if_cong)
  also have \<open>\<dots> \<le> (\<integral>\<tau>. (if card(state_\<chi> \<tau>) < thresh then aux S \<tau> else aux S \<tau>) \<partial>p)\<close>
    using c by (intro integral_mono_AE AE_pmfI) auto
  also have \<open>\<dots> = (\<integral>\<tau>. aux S \<tau> \<partial>p)\<close> by simp
  also have \<open>\<dots> \<le> \<phi> 1 True ^ card S\<close> using 3(2) unfolding p_def by (intro 3(1)) auto
  finally show ?case by simp
qed

text \<open>Lemma~\ref{le:neg_cor_neg}:\<close>
lemma run_steps_preserves_expectation_le' :
  fixes q :: real and h :: \<open>real \<Rightarrow> real\<close>
  assumes h:
    \<open>0 < q\<close> \<open>q \<le> 1\<close> 
    \<open>concave_on {0 .. 1 / q} h\<close> 
    \<open>\<And> x. \<lbrakk>0 \<le> x; x * q \<le> 1\<rbrakk> \<Longrightarrow> h x \<ge> 0\<close>
  defines
    \<open>aux \<equiv> \<lambda>S \<sigma>. (\<Prod>x \<in> S. of_bool (state_p \<sigma> \<ge> q) * h (of_bool (x \<in> state_\<chi> \<sigma>) / state_p \<sigma>))\<close>

  assumes \<open>S \<subseteq> run_state_set \<rho>\<close>
  shows \<open>(\<integral>\<tau>. aux S \<tau> \<partial>run_state_pmf \<rho>) \<le> (h 1) ^ card S\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  define \<phi> where \<open>\<phi> = (\<lambda>p e. of_bool (q \<le> p) * h(of_bool e / p))\<close>
  have \<phi>_1: \<open>\<phi> x b \<ge> 0\<close> if \<open>x > 0\<close> \<open>x \<le> 1\<close> for x b
    using h(1,4) that unfolding \<phi>_def by simp 
  have \<phi>_2: \<open>\<phi> x True * p + \<phi> x False * (1 - p) \<le> \<phi> (x / p) True\<close> if \<open>x \<in> {0<..1}\<close> \<open>p \<in> {0<..1}\<close> 
    for x p
  proof (cases \<open> 1 / x \<in> {0..1 / q}\<close>)
    case True
    hence a:\<open>q \<le> x\<close> using that(1) h(1) by (simp add:divide_simps) 
    also have \<open>\<dots> \<le> x/p\<close> using that by (auto simp add:divide_simps) 
    finally have b:\<open>q \<le> x / p\<close> by simp
    show ?thesis
      unfolding \<phi>_def using that concave_onD[OF h(3) _ _ _ True, where t=\<open>p\<close> and x=\<open>0\<close>] a b h(1)
      by (auto simp:algebra_simps) 
  next
    case False
    hence a:\<open>q > x\<close> using that h(1) by (auto simp add:divide_simps)
    hence \<open>q \<le> x/p \<Longrightarrow> 0 \<le> h (p / x)\<close> using that by (intro h(4)) (auto simp:field_simps)
    thus ?thesis using a by (simp add:\<phi>_def)
  qed
  have \<phi>_3: \<open>\<phi> x False \<le> \<phi> y False\<close> if \<open>x \<le> y\<close> for x y
     using that by (auto intro:h(4) simp add:\<phi>_def) 

  have \<open>?L = (\<integral>\<tau>. (\<Prod>x\<in>S. \<phi> (f ^ state_k \<tau>) (x \<in> state_\<chi> \<tau>)) \<partial>run_state_pmf \<rho>)\<close>
    unfolding \<phi>_def by (simp add:state_p_def aux_def)
  also have \<open>\<dots> \<le> \<phi> 1 True^ card S\<close> using \<phi>_1 \<phi>_2 \<phi>_3
    by (intro run_steps_preserves_expectation_le assms ) (auto intro:mono_onI)
  also have \<open>\<dots> = h 1 ^ card S\<close> using h unfolding \<phi>_def by simp
  finally show ?thesis by simp
qed

text \<open>Analysis of the case where @{term \<open>card (set xs) \<ge> thresh\<close>}:\<close>

context
  fixes xs :: \<open>'a list\<close>
  assumes set_larger_than_threshold: \<open>card (set xs) \<ge> thresh\<close>
begin

definition \<open>q = real thresh / (4 * card (set xs))\<close>

lemma q_range: \<open>q \<in> {0<..1/4}\<close>
  using set_larger_than_threshold thresh_gt_0 unfolding q_def by auto

lemma upper_tail_bound_helper:
  assumes \<open>x \<in> {0<..1::real}\<close>
  defines \<open>h \<equiv> (\<lambda>x. - q * x\<^sup>2 / 3 - ln (1 + q * x) + q * ln (1 + x) * (1 + x))\<close>
  shows \<open>h x \<ge> 0\<close>
proof -
  define h' where \<open>h' x = -2*x*q/3 - q/(1+q*x) + q*ln(1+x) + q\<close> for x

  have deriv: \<open>(h has_real_derivative (h' x)) (at x)\<close> if \<open>x \<ge> 0\<close> \<open>x \<le> 1\<close> for x
  proof -
    have \<open>0 < (1::real) + 0\<close> by simp
    also have \<open>\<dots> \<le> 1 + q * x\<close> using that q_range by (intro add_mono mult_nonneg_nonneg) auto
    finally have \<open>0 < 1 + q * x\<close> by simp
    thus ?thesis
      using that q_range unfolding h_def h'_def power2_eq_square
      by (auto intro!:derivative_eq_intros)
  qed

  have deriv_nonneg: \<open>h' x \<ge> 0\<close> if \<open>x \<ge> 0\<close> \<open>x \<le> 1\<close> for x
  proof -
    have \<open>exp(2*x/3) = exp((1-x)*\<^sub>R 0 + x *\<^sub>R (2/3))\<close> by simp
    also have \<open>\<dots> \<le> (1-x)*exp 0 + x*exp(2/3)\<close> by (intro that convex_onD[OF exp_convex]) auto
    also have \<open>\<dots> = 1 + x*(exp (2/3)-exp 0)\<close> by (simp add:algebra_simps)
    also have \<open>\<dots> \<le> 1+ x* 1\<close> by (intro add_mono order.refl mult_left_mono that) (approximation 5)
    finally have \<open>exp(2*x/3) \<le> exp(ln(1+x))\<close> using that by simp
    hence \<open>0 \<le> ln(1+x) - 2*x/3\<close> by simp
    also have \<open>\<dots> = ln(1+x) +1 -2*x/3 - 1\<close> by simp
    also have \<open>\<dots> \<le> ln(1+x) +1 -2 * x/3 - 1/(1+q*x)\<close>
      using q_range that by (intro add_mono diff_mono) (auto simp:divide_simps)
    finally have b: \<open>0 \<le> ln(1+x) +1 -2 * x/3 - 1/(1+q*x)\<close> by simp

    have \<open>h' x = q * (-2 * x/3 - 1/(1+q*x) +ln(1+x) +1)\<close>
      unfolding h'_def by (simp add:algebra_simps)
    also have \<open>\<dots> \<ge> 0\<close>  using b q_range by (intro mult_nonneg_nonneg) auto
    finally show ?thesis by simp
  qed

  have h_mono: \<open>h x \<le> h y\<close> if \<open>x \<le> y\<close> \<open>x \<ge> 0\<close> \<open>y \<le> 1\<close> for x y
    using deriv deriv_nonneg order_trans[OF _ that(3)] order_trans[OF that(2)]
    by (intro DERIV_nonneg_imp_nondecreasing[OF that(1)]) blast

  show ?thesis
  proof -
    have \<open>0 = h 0\<close> unfolding h_def by simp
    also have \<open>\<dots> \<le> h x\<close> using assms(1) by (intro h_mono)  auto
    finally show ?thesis by simp
  qed
qed

text \<open>Lemma \ref{le:upper_tail}:\<close>
lemma upper_tail_bound:
  assumes \<open>\<epsilon> \<in> {0<..1::real}\<close>
  assumes \<open>run_state_set \<rho> \<subseteq> set xs\<close>
  shows \<open>measure (run_state_pmf \<rho>) {\<omega>. estimate \<omega> \<ge> (1 + \<epsilon>) * card (set xs) \<and> state_p \<omega> \<ge> q}
    \<le> exp(-real thresh/12 * \<epsilon>^2)\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  let ?p = \<open>run_state_pmf \<rho>\<close>
  define t where \<open>t = q * ln (1+\<epsilon>)\<close>
  define h where \<open>h x = 1 + q * x * (exp (t / q) - 1)\<close> for x

  let ?A' = \<open>run_state_set \<rho>\<close>
  note [simp] = integrable_measure_pmf_finite[OF finite_run_state_pmf]

  let ?X = \<open>\<lambda>i \<omega>. of_bool (i \<in> state_\<chi> \<omega>) / state_p \<omega>\<close>
  let ?c = \<open>real (card (set xs))\<close>

  have t_gt_0: \<open>t > 0\<close> unfolding t_def using q_range assms(1) by auto

  have mono_exp_t: \<open>strict_mono (\<lambda>(x::real). exp (t * x))\<close>
    using t_gt_0 by (intro strict_monoI) auto

  have h_1_eq: \<open>h 1 = 1 + q * \<epsilon>\<close> using assms(1) unfolding h_def t_def by simp
  have h_1_pos: \<open>h 1 \<ge> 1\<close> unfolding h_1_eq using q_range assms(1) by auto

  have a: \<open>ln (h 1) - t * (1 + \<epsilon>) \<le> - q * \<epsilon>^2 / 3\<close>
    using upper_tail_bound_helper[OF assms(1)] 
    unfolding h_1_eq t_def by (simp add:algebra_simps)

  have b: \<open>exp (t / y) \<le> h (1 / y)\<close> if \<open>y \<ge> q\<close> for y
  proof -
    have \<open>exp (t / y) = exp ((1-q/y) *\<^sub>R 0 + (q/y) *\<^sub>R (t/q))\<close> using q_range by simp
    also have \<open>\<dots> \<le> (1-q/y) * exp 0 + (q/y) * exp (t/q)\<close> using that q_range
      by (intro convex_onD[OF exp_convex]) simp_all
    also have \<open>\<dots> = h (1 / y)\<close> unfolding h_def by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have c: \<open>1 \<le> h 0\<close> unfolding h_def by simp

  have h_concave: \<open>concave_on {0..1 / q} h\<close>
    unfolding h_def by (intro concave_on_linorderI) (auto simp:algebra_simps)

  have h_nonneg: \<open>h y \<ge> 0\<close> if \<open>y \<in> {0..1/q}\<close> for y
  proof -
    have \<open>0 \<le> (1-q*y) + q*y * 0\<close> using that q_range by (auto simp:field_simps)
    also have \<open>\<dots> \<le> (1-q*y) + q*y*exp(t/q)\<close> using that q_range
      by (intro add_mono mult_left_mono mult_nonneg_nonneg) auto
    also have \<open>\<dots> = h y\<close> unfolding h_def by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have \<open>?L = measure ?p {\<omega>. exp (t * estimate \<omega>) \<ge> exp (t*((1+\<epsilon>)* ?c))\<and>state_p \<omega>\<ge> q}\<close>
    by (subst strict_mono_less_eq[OF mono_exp_t]) simp
  also have \<open>\<dots> \<le> \<P>(\<omega> in ?p. of_bool(state_p \<omega> \<ge> q)*exp (t*estimate \<omega>)\<ge> exp (t*((1+\<epsilon>)*?c)))\<close>
    by (intro pmf_mono) auto
  also have \<open>\<dots> \<le> (\<integral>\<omega>. of_bool(state_p \<omega> \<ge> q)* exp (t*estimate \<omega>)\<partial>?p) / exp (t*((1+\<epsilon>)*?c))\<close>
    by (intro integral_Markov_inequality_measure[where A=\<open>{}\<close>]) simp_all
  also have \<open>\<dots> = (\<integral>\<omega>. of_bool(state_p \<omega> \<ge> q) * exp((\<Sum>i\<in>?A'. t * ?X i \<omega>)) \<partial>?p)/exp(t*((1+\<epsilon>)*?c))\<close>
    using state_\<chi>_run_state_pmf[where \<rho>=\<open>\<rho>\<close>] Int_absorb1
    unfolding sum_divide_distrib[symmetric] sum_distrib_left[symmetric] estimate_def state_p_def
    by (intro integral_cong_AE arg_cong2[where f=\<open>(/)\<close>])
      (auto simp:AE_measure_pmf_iff intro!:arg_cong[where f=\<open>card\<close>])
  also have \<open>\<dots> \<le> (\<integral>\<omega>. (\<Prod>i \<in> ?A'. of_bool(state_p \<omega> \<ge> q)*exp( t* ?X i \<omega>)) \<partial>?p)/ exp(t*((1+\<epsilon>)*?c))\<close>
    unfolding exp_sum[OF finite_run_state_set] prod.distrib
    by (intro divide_right_mono integral_mono_AE AE_pmfI)
      (auto intro!:mult_nonneg_nonneg prod_nonneg)
  also have \<open>\<dots> \<le> (\<integral>\<omega>. (\<Prod>i \<in> ?A'. of_bool(state_p \<omega> \<ge> q)*h( ?X i \<omega>)) \<partial>?p)/ exp (t*((1+\<epsilon>)*?c))\<close>
    using b c by (intro divide_right_mono integral_mono_AE AE_pmfI) (auto intro!:prod_mono)
  also have \<open>\<dots> \<le> h 1 ^ card ?A' / exp (t * ((1+\<epsilon>)* ?c))\<close>
    using q_range h_concave
    by (intro divide_right_mono run_steps_preserves_expectation_le')
      (auto intro!:h_nonneg simp:field_simps)
  also have \<open>\<dots> \<le> h 1 powr ?c / exp (t * ((1+\<epsilon>)* ?c))\<close>
    using card_mono[OF _ assms(2)] h_1_pos
    by (subst powr_realpow) (auto intro!:power_increasing divide_right_mono)
  also have \<open>\<dots> = exp (?c * (ln (h 1) - t * (1 + \<epsilon>)))\<close>
    using h_1_pos unfolding powr_def by (simp add:algebra_simps exp_diff)
  also have \<open>\<dots> \<le> exp (?c * (-q * \<epsilon>^2/3))\<close>
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono a) simp
  also have \<open>\<dots> = ?R\<close> using set_larger_than_threshold thresh_gt_0 unfolding q_def by auto
  finally show ?thesis by simp
qed

(* Lemma 5 *)
text \<open>Lemma~\ref{le:low_p}:\<close>
lemma q_bound: \<open>measure (run_steps xs) {\<sigma>. state_p \<sigma> < q} \<le> real (length xs) * exp(-real thresh/12)\<close>
proof -
  define \<rho> where \<open>\<rho> = FinalState xs\<close>

  define j where \<open>j = nat \<lfloor>log f q\<rfloor>\<close>

  have f_range': \<open>f \<ge> 0\<close> \<open>f \<le> 1\<close> using f_range by auto

  have \<open>q = f powr (log f q)\<close>
    using f_range q_range by (intro powr_log_cancel[symmetric]) auto
  also have \<open>\<dots> \<le> f powr (\<lfloor>log f q\<rfloor>)\<close> using f_range by (intro powr_mono') auto
  also have \<open>\<dots> \<le> f powr (real (nat \<lfloor>log f q\<rfloor>))\<close> using f_range q_range
    by (subst of_nat_int_floor) (auto intro:divide_nonpos_neg simp add:log_def)
  also have \<open>\<dots> = f ^ j\<close> using f_range unfolding j_def by (subst powr_realpow) auto
  finally have f_1: \<open>q \<le> f^j\<close> by simp

  have \<open>f^(j+1) = f powr (real (nat \<lfloor>log f q\<rfloor>+1))\<close>
    unfolding j_def using f_range by (subst powr_realpow) auto
  also have \<open>\<dots> \<le> f powr (log f q)\<close> by (intro powr_mono' f_range') linarith+
  also have \<open>\<dots> = q\<close> using f_range q_range by (intro powr_log_cancel) auto
  finally have f_2: \<open>f^(j+1) \<le> q\<close> by simp

  have \<open>2 * real (card (set xs)) * f^j \<le> 4*f* real (card (set xs)) * f^j\<close>
    using f_range by (intro mult_right_mono) auto
  also have \<open>\<dots> = 4 * real (card (set xs)) * f^(j+1)\<close> by simp
  also have \<open>\<dots> \<le> 4 * real (card (set xs)) * q\<close> using f_2 by (intro mult_left_mono) auto
  also have \<open>\<dots> = thresh\<close> using thresh_gt_0 set_larger_than_threshold unfolding q_def by auto
  finally have f_3: \<open>2 * real (card (set xs)) * f^j \<le> thresh\<close> by simp

  have ih: \<open>run_state_set \<rho> \<subseteq> set xs\<close> unfolding \<rho>_def by simp

  have \<open>n > j\<close> if \<open>f^n < q\<close> for n
    unfolding not_le[symmetric] using that f_1 power_decreasing[OF _ f_range'] by force
  hence \<open>measure (run_steps xs) {\<omega>. state_p \<omega> < q} \<le> measure (run_state_pmf \<rho>) {\<omega>. state_k \<omega> > j}\<close>
    unfolding \<rho>_def run_state_pmf.simps by (intro pmf_mono) (auto simp:state_p_def)
  also have \<open>\<dots> \<le> real (len_run_state \<rho>) * exp(- real thresh/12)\<close>
    using ih
  proof (induction \<rho> rule:run_state_induct)
    case 1
    then show ?case using q_range by (simp add:run_steps_def state_p_def initial_state_def)
  next
    case (2 ys x)
    have \<open>measure (step_1 x s) {\<omega>. state_k \<omega> > j} = indicator {\<omega>. state_k \<omega> > j} s\<close>
      for s :: \<open>'a state\<close>
      by (simp add:step_1_def map_pmf_def[symmetric] Let_def)

    thus ?case using 2 by (simp add:measure_bind_pmf)
  next
    case (3 ys x)
    define p where \<open>p = run_state_pmf (IntermState ys x)\<close>

    have \<open>finite (set_pmf p)\<close> unfolding p_def by (intro finite_run_state_pmf)
    note [simp] = integrable_measure_pmf_finite[OF this]

    have b: \<open>run_state_pmf (FinalState (ys@[x])) = p \<bind> step_2\<close>
      by (simp add:run_steps_snoc p_def)

    have d: \<open>run_state_set (IntermState ys x) \<subseteq> set xs\<close>
      using 3(2) by simp

    have a':\<open>measure (step_2 \<sigma>) {\<sigma>. state_k \<sigma> > j} \<le>
      indicator {\<sigma>. state_k \<sigma> > j \<or> card (state_\<chi> \<sigma>) \<ge> thresh \<and> state_k \<sigma> = j} \<sigma>\<close>
      for j and \<sigma> :: \<open>'a state\<close>
      by (simp add:step_2_def Let_def indicator_def map_pmf_def[symmetric])

    have a:\<open>measure (step_2 \<sigma>) {\<sigma>. state_p \<sigma> < q} \<le>
      indicator {\<sigma>. state_p \<sigma> < q \<or> card (state_\<chi> \<sigma>) \<ge> thresh} \<sigma>\<close>
      for \<sigma> :: \<open>'a state\<close>
      by (simp add:step_2_def Let_def indicator_def)

    have \<open>measure p {\<sigma>. card (state_\<chi> \<sigma>) \<ge> thresh \<and> state_k \<sigma> = j} \<le>
      measure p {\<sigma>. (1+1) * real(card(set xs)) \<le> estimate \<sigma> \<and> q \<le> state_p \<sigma>}\<close>
      using f_1 f_3 f_range by (intro pmf_mono) (simp add:estimate_def state_p_def field_simps)
    also have \<open>\<dots> \<le> exp (- real thresh / 12 * 1^2)\<close>
      unfolding p_def by (intro upper_tail_bound d) simp
    finally have c:
      \<open>measure p {\<sigma>. card (state_\<chi> \<sigma>) \<ge> thresh \<and> state_k \<sigma> = j} \<le> exp (- real thresh / 12)\<close>
      by simp

    have \<open>measure (run_state_pmf (FinalState (ys @ [x]))) {\<omega>. state_k \<omega> > j} =
      (\<integral>s. measure (step_2 s) {\<omega>. state_k \<omega> > j} \<partial>p)\<close>
      unfolding b by (simp add:measure_bind_pmf)
    also have \<open>\<dots> \<le> (\<integral>s. indicator {\<omega>. state_k \<omega>>j \<or> card(state_\<chi> \<omega>) \<ge> thresh \<and> state_k \<omega>=j} s \<partial>p)\<close>
      by (intro integral_mono_AE AE_pmfI a') simp_all
    also have \<open>\<dots> = measure p {\<omega>. state_k \<omega> > j \<or> card (state_\<chi> \<omega>) \<ge> thresh \<and> state_k \<omega> = j}\<close>
      by simp
    also have \<open>\<dots> \<le>
      measure p {\<omega>. state_k \<omega> > j} +
      measure p {\<omega>. card (state_\<chi> \<omega>) \<ge> thresh \<and> state_k \<omega> = j}\<close>
      by (intro pmf_add) auto
    also have \<open>\<dots> \<le> length ys * exp (- real thresh / 12) + exp (- real thresh / 12)\<close>
      using 3(1)[OF d] by (intro add_mono c) (simp add:p_def)
    also have \<open>\<dots> = real (len_run_state (FinalState (ys @ [x]))) * exp (- real thresh / 12)\<close>
      by (simp add:algebra_simps)
    finally show ?case by simp
  qed
  also have \<open>\<dots> = real (length xs) * exp(- real thresh/12)\<close> by (simp add:\<rho>_def)
  finally show ?thesis by simp
qed

lemma lower_tail_bound_helper:
  assumes \<open>x \<in> {0<..<1::real}\<close>
  defines \<open>h \<equiv> (\<lambda>x. - q * x\<^sup>2 / 2 - ln (1 - q * x) + q * ln (1 - x) * (1 - x))\<close>
  shows \<open>h x \<ge> 0\<close>
proof -
  define h' where \<open>h' x = -x*q + q/(1-q*x) - q*ln(1-x) - q\<close> for x

  have deriv: \<open>(h has_real_derivative (h' x)) (at x)\<close> if \<open>x \<ge> 0\<close> \<open>x < 1\<close> for x
  proof -
    have \<open>q * x \<le> (1/4) * 1\<close> using that q_range by (intro mult_mono) auto
    also have \<open>\<dots> < 1\<close> by simp
    finally have \<open>q * x < 1\<close> by simp
    thus ?thesis
      using that q_range unfolding h_def h'_def power2_eq_square
      by (auto intro!:derivative_eq_intros)
  qed

  have deriv_nonneg: \<open>h' x \<ge> 0\<close> if \<open>x \<ge> 0\<close> \<open>x < 1\<close> for x
  proof -
    have \<open>q * x \<le> (1/4) * 1\<close> using that q_range by (intro mult_mono) auto
    also have \<open>\<dots> < 1\<close> by simp
    finally have a:\<open>q * x < 1\<close> by simp

    have \<open>0 \<le> - ln (1 - x) - x\<close> using ln_one_minus_pos_upper_bound[OF that] by simp
    also have \<open>\<dots> = - ln (1 - x) - 1 - x + 1\<close> by simp
    also have \<open>\<dots> \<le> - ln (1 - x) - 1 - x + 1 / (1 - q * x)\<close>
      using a q_range that by (intro add_mono diff_mono) (auto simp:divide_simps)
    finally have b: \<open>0 \<le> - ln (1 - x) - 1 - x + 1 / (1 - q * x)\<close> by simp

    have \<open>h' x = q * (-x + 1 / (1 - q * x) - ln (1 - x) - 1)\<close>
      unfolding h'_def by (simp add:algebra_simps)
    also have \<open>\<dots> \<ge> 0\<close>  using b q_range by (intro mult_nonneg_nonneg) auto
    finally show ?thesis by simp
  qed

  have h_mono: \<open>h x \<le> h y\<close> if \<open>x \<le> y\<close> \<open>x \<ge> 0\<close> \<open>y < 1\<close> for x y
    using deriv deriv_nonneg le_less_trans[OF _ that(3)] order_trans[OF that(2)]
    by (intro DERIV_nonneg_imp_nondecreasing[OF that(1)]) blast

  show \<open>h x \<ge> 0\<close>
  proof -
    have \<open>0 = h 0\<close> unfolding h_def by simp
    also have \<open>\<dots> \<le> h x\<close> using assms(1) by (intro h_mono)  auto
    finally show ?thesis by simp
  qed
qed

text \<open>Lemma~\ref{le:lower_tail}:\<close>
lemma lower_tail_bound:
  assumes \<open>\<epsilon> \<in> {0<..<1::real}\<close>
  shows \<open>measure (run_steps xs) {\<omega>. estimate \<omega> \<le> (1 - \<epsilon>) * card (set xs) \<and> state_p \<omega> \<ge> q}
    \<le> exp(-real thresh/8 * \<epsilon>^2)\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  let ?p = \<open>run_state_pmf (FinalState xs)\<close>
  define t where \<open>t = q * ln (1-\<epsilon>)\<close>
  define h where \<open>h x = 1 + q * x * (exp (t / q) - 1)\<close> for x

  let ?A' = \<open>set xs\<close>
  have \<open>finite (set_pmf (run_steps xs))\<close>
    using finite_run_state_pmf[where \<rho>=\<open>FinalState xs\<close>] by simp
  note [simp] = integrable_measure_pmf_finite[OF this]

  let ?X = \<open>\<lambda>i \<omega>. of_bool(i \<in> state_\<chi> \<omega>)/state_p \<omega>\<close>
  let ?c = \<open>real (card (set xs))\<close>

  have t_lt_0: \<open>t < 0\<close>
    unfolding t_def using q_range assms(1) by (intro mult_pos_neg ln_less_zero) auto

  have mono_exp_t: \<open>exp (t * x) \<le> exp (t * y) \<longleftrightarrow> y \<le> x\<close> for x y
    using t_lt_0 by auto

  have h_1_eq: \<open>h 1 = 1 - q * \<epsilon>\<close> using assms(1) unfolding h_def t_def by simp
  have \<open>\<epsilon> * (q * 4) \<le> 1 * 1\<close> using q_range assms(1) by (intro mult_mono) auto
  hence h_1_pos: \<open>h 1 \<ge> 3/4\<close> unfolding h_1_eq by (auto simp:algebra_simps)

  have a: \<open>ln (h 1) - t * (1 - \<epsilon>) \<le> - q * \<epsilon>^2 / 2\<close>
    unfolding h_1_eq t_def using lower_tail_bound_helper[OF assms(1)]
    by (simp add:divide_simps)

  have b: \<open>exp (t / y) \<le> h (1 / y)\<close> if \<open>y \<ge> q\<close> for y
  proof -
    have \<open>exp (t / y) = exp ((1-q/y) *\<^sub>R 0 + (q/y) *\<^sub>R (t/q))\<close> using q_range by simp
    also have \<open>\<dots> \<le> (1-q/y) * exp 0 + (q/y) * exp (t/q)\<close> using that q_range
      by (intro convex_onD[OF exp_convex]) simp_all
    also have \<open>\<dots> = h (1 / y)\<close> unfolding h_def by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have c: \<open>1 \<le> h 0\<close> unfolding h_def by simp

  have h_concave: \<open>concave_on {0..1 / q} h\<close>
    unfolding h_def by (intro concave_on_linorderI) (auto simp:algebra_simps)

  have h_nonneg: \<open>h y \<ge> 0\<close> if \<open>y \<in> {0..1/q}\<close> for y
  proof -
    have \<open>0 \<le> (1 - q * y) + q * y * 0\<close> using that q_range by (auto simp:field_simps)
    also have \<open>\<dots> \<le> (1 - q * y) + q * y * exp(t / q)\<close> using that q_range
      by (intro add_mono mult_left_mono mult_nonneg_nonneg) auto
    also have \<open>\<dots> = h y\<close> unfolding h_def by (simp add:algebra_simps)
    finally show ?thesis by simp
  qed

  have \<open>?L = measure ?p {\<omega>. exp (t * estimate \<omega>) \<ge> exp (t * ((1-\<epsilon>) * ?c)) \<and> state_p \<omega> \<ge> q}\<close>
    by (subst  mono_exp_t) simp
  also have \<open>\<dots> \<le> \<P>(\<omega> in ?p. of_bool(state_p \<omega> \<ge> q)*exp (t * estimate \<omega>)\<ge> exp (t * ((1-\<epsilon>) * ?c)))\<close>
    by (intro pmf_mono) auto
  also have \<open>\<dots> \<le> (\<integral>\<omega>. of_bool(state_p \<omega> \<ge> q)* exp (t * estimate \<omega>)\<partial>?p) / exp (t * ((1-\<epsilon>) * ?c))\<close>
    by (intro integral_Markov_inequality_measure[where A=\<open>{}\<close>]) simp_all
  also have \<open>\<dots> = (\<integral>\<omega>. of_bool(state_p \<omega> \<ge> q) * exp((\<Sum>i\<in>?A'. t * ?X i \<omega>)) \<partial>?p)/exp(t*((1-\<epsilon>)*?c))\<close>
    using state_\<chi>_run_state_pmf[where \<rho>=\<open>FinalState xs\<close>] Int_absorb1 
    unfolding sum_divide_distrib[symmetric] sum_distrib_left[symmetric] estimate_def state_p_def
    by (intro integral_cong_AE arg_cong2[where f=\<open>(/)\<close>])
      (auto simp:AE_measure_pmf_iff intro!:arg_cong[where f=\<open>card\<close>])
  also have \<open>\<dots> \<le> (\<integral>\<omega>. (\<Prod>i \<in> ?A'. of_bool(state_p \<omega> \<ge> q)*exp( t* ?X i \<omega>)) \<partial>?p)/ exp(t*((1-\<epsilon>)*?c))\<close>
    unfolding exp_sum[OF finite_set] prod.distrib
    by (intro divide_right_mono integral_mono_AE AE_pmfI)
     (auto intro!:mult_nonneg_nonneg prod_nonneg)
  also have \<open>\<dots> \<le> (\<integral>\<omega>. (\<Prod>i \<in> ?A'. of_bool(state_p \<omega> \<ge> q)*h (?X i \<omega>)) \<partial>?p)/ exp (t * ((1-\<epsilon>)*?c))\<close>
    using b c by (intro divide_right_mono integral_mono_AE AE_pmfI) (auto intro!:prod_mono)
  also have \<open>\<dots> \<le> h 1 ^ card ?A' / exp (t * ((1 - \<epsilon>) * ?c))\<close>
    using q_range h_concave
    by (intro divide_right_mono run_steps_preserves_expectation_le')
      (auto intro!:h_nonneg simp:field_simps)
  also have \<open>\<dots> \<le> h 1 powr ?c / exp (t * ((1 - \<epsilon>) * ?c))\<close>
    using h_1_pos by (subst powr_realpow) (auto intro!:power_increasing divide_right_mono)
  also have \<open>\<dots> = exp (?c * (ln (h 1) - t * (1 - \<epsilon>)))\<close>
    using h_1_pos unfolding powr_def by (simp add:algebra_simps exp_add[symmetric] exp_diff)
  also have \<open>\<dots> \<le> exp (?c * (- q * \<epsilon> ^ 2 / 2))\<close>
    by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono a) simp
  also have \<open>\<dots> = ?R\<close> using set_larger_than_threshold thresh_gt_0 unfolding q_def by auto
  finally show ?thesis by simp
qed

lemma correctness_aux:
  fixes \<epsilon> \<delta> :: real
  assumes \<open>\<epsilon> \<in> {0<..<1}\<close> \<open>\<delta> \<in> {0<..<1}\<close>
  assumes \<open>real thresh \<ge> 12/\<epsilon>^2 * ln (3*real (length xs) /\<delta>)\<close>
  defines \<open>R \<equiv> real (card (set xs))\<close>
  shows \<open>measure (run_steps xs) {\<omega>. \<bar>estimate \<omega> - R\<bar> > \<epsilon>*R } \<le> \<delta>\<close> 
    (is \<open>?L \<le> ?R\<close>)
proof -
  let ?pmf = \<open>run_steps xs\<close>
  let ?pmf' = \<open>run_state_pmf (FinalState xs)\<close>
  let ?p = \<open>state_p\<close> 
  let ?l = \<open>real (length xs)\<close>
  have l_gt_0: \<open>length xs > 0\<close> using set_larger_than_threshold thresh_gt_0 by auto
  hence l_ge_1: \<open>?l \<ge> 1\<close>  by linarith

  have d:\<open>ln (3*real (length xs) /\<delta>) = - ln (\<delta>/(3*?l))\<close>
    using l_ge_1 assms(2) by (subst (1 2) ln_div) auto

  have \<open>exp (- real thresh / 12 * 1) \<le> exp (- real thresh / 12 * \<epsilon>^2)\<close>
    using assms(1) by (intro iffD2[OF exp_le_cancel_iff] mult_left_mono_neg power_le_one) auto
  also have \<open>\<dots> \<le>  \<delta> / (3 * ?l)\<close>
    using assms(1-3) l_ge_1 unfolding d by (subst ln_ge_iff[symmetric]) (auto simp:divide_simps)
  finally have \<open>exp (- real thresh / 12) \<le> \<delta> / (3*?l)\<close> by simp
  hence a: \<open>?l * exp (- real thresh / 12) \<le> \<delta> / 3\<close> using l_gt_0 by (auto simp:field_simps) 

  have c: \<open>exp(-real thresh/12 * \<epsilon>^2) \<le> \<delta> / (3*?l)\<close>
    using assms(1-3) l_ge_1 unfolding d by (subst ln_ge_iff[symmetric]) (auto simp:divide_simps)
  also have \<open>\<dots> \<le> \<delta> / 3\<close>
    using assms(1-3) l_ge_1 by (intro divide_left_mono) auto
  finally have c: \<open>exp(-real thresh/12 * \<epsilon>^2) \<le> \<delta> / 3\<close> by simp

  have \<open>exp(-real thresh/8 * \<epsilon>^2) \<le> exp(-real thresh/12 * \<epsilon>^2)\<close>
    by (intro iffD2[OF exp_le_cancel_iff]) auto
  also have \<open>\<dots> \<le> \<delta>/3\<close> using c by simp
  finally have b: \<open>exp(-real thresh/8 * \<epsilon>^2) \<le> \<delta> / 3\<close> by simp

  have \<open>?L \<le> measure ?pmf {\<omega>. \<bar>estimate \<omega> - R\<bar> \<ge> \<epsilon> * R}\<close>
    by (intro pmf_mono) auto
  also have \<open>\<dots> \<le> measure ?pmf {\<omega>. \<bar>estimate \<omega> - R\<bar> \<ge> \<epsilon>*R \<and> ?p \<omega> \<ge> q} + measure ?pmf {\<omega>. ?p \<omega> < q}\<close>
    by (intro pmf_add) auto
  also have \<open>\<dots> \<le> measure ?pmf {\<omega>. (estimate \<omega> \<le> (1-\<epsilon>) * R \<or> estimate \<omega> \<ge> (1+\<epsilon>) * R) \<and> ?p \<omega> \<ge> q} +
    ?l * exp(-real thresh/12)\<close>
    by (intro pmf_mono add_mono q_bound) (auto simp:abs_real_def algebra_simps split:if_split_asm)
  also have \<open>\<dots> \<le> measure ?pmf {\<omega>. estimate \<omega> \<le> (1-\<epsilon>) *R \<and> ?p \<omega> \<ge> q} + 
    measure ?pmf' {\<omega>. estimate \<omega> \<ge> (1+\<epsilon>) * R \<and> ?p \<omega> \<ge> q} + \<delta>/3\<close>
    unfolding run_state_pmf.simps by (intro add_mono pmf_add a) auto
  also have \<open>\<dots> \<le> exp(-real thresh/8 * \<epsilon> ^ 2) + exp(-real thresh/12 * \<epsilon> ^ 2) + \<delta> / 3\<close>
    unfolding R_def using assms(1) by (intro upper_tail_bound add_mono lower_tail_bound) auto
  also have \<open>\<dots> \<le> \<delta> / 3 +  \<delta> / 3 + \<delta> / 3\<close> by (intro  add_mono b c) auto
  finally show ?thesis by simp
qed

end

lemma deterministic_phase:
  assumes \<open>card (run_state_set \<sigma>) < thresh\<close>
  shows \<open>run_state_pmf \<sigma> = return_pmf \<lparr> state_k = 0, state_\<chi> = run_state_set \<sigma> \<rparr>\<close>
  using assms
proof (induction \<sigma> rule:run_state_induct)
  case 1 thus ?case by (simp add:run_steps_def initial_state_def)
next
  case (2 xs x)
  have \<open>card (set xs) < thresh\<close> using 2(2) by (simp add:card_insert_if) presburger 
  moreover have \<open>bernoulli_pmf 1 = return_pmf True\<close>
    by (intro pmf_eqI) (auto simp:bernoulli_pmf.rep_eq)
  ultimately show ?case using 2(1) by (simp add:step_1_def bind_return_pmf)
next
  case (3 xs x)
  let ?p = \<open>run_state_pmf (IntermState xs x)\<close>
  have a: \<open>card (run_state_set (IntermState xs x)) < thresh\<close> using 3(2) by simp 
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = ?p \<bind> step_2\<close>
    by (simp add:run_steps_snoc)
  show ?case
    using 3(2) unfolding b 3(1)[OF a] by (simp add:step_2_def bind_return_pmf Let_def)
qed

text \<open>Theorem~\ref{th:concentration}:\<close>
theorem correctness:
  fixes \<epsilon> \<delta> :: real
  assumes \<open>\<epsilon> \<in> {0<..<1}\<close> \<open>\<delta> \<in> {0<..<1}\<close>
  assumes \<open>real thresh \<ge> 12 / \<epsilon> ^ 2 * ln (3 * real (length xs) / \<delta>)\<close>
  defines \<open>R \<equiv> real (card (set xs))\<close>
  shows \<open>measure (run_steps xs) {\<omega>. \<bar>estimate \<omega> - R\<bar> > \<epsilon> * R} \<le> \<delta>\<close> 
proof (cases \<open>card (set xs) \<ge> thresh\<close>)
  case True
  show ?thesis
    unfolding R_def by (intro correctness_aux True assms)
next
  case False
  hence \<open>run_steps xs = return_pmf \<lparr> state_k = 0, state_\<chi> = (set xs) \<rparr>\<close>
    using deterministic_phase[where \<sigma>=\<open>FinalState xs\<close>] by simp
  thus ?thesis using assms(1,2) by (simp add:indicator_def state_p_def estimate_def R_def not_less)
qed

lemma state_k_run_state_pmf:
  fixes \<rho> :: \<open>'a run_state\<close>
  shows \<open>AE \<omega> in run_state_pmf \<rho>. state_k \<omega> \<le> len_run_state \<rho>\<close>
proof (induction \<rho> rule:run_state_induct)
  case 1 thus ?case by (simp add:run_steps_def AE_measure_pmf_iff initial_state_def)
next
  case (2 xs x)
  then show ?case by (simp add:AE_measure_pmf_iff step_1_def Let_def remove_def)
next
  case (3 xs x)
  let ?p = \<open>run_state_pmf (IntermState xs x)\<close>
  have b: \<open>run_state_pmf (FinalState (xs@[x])) = ?p \<bind> step_2\<close>
    by (simp add:run_steps_snoc)

  thus ?case using 3
    apply (simp add:AE_measure_pmf_iff step_2_def Let_def)
    using le_SucI by blast
qed

lemma run_steps_expectation_sing:
  assumes i: \<open>i \<in> set xs\<close>
  shows \<open>measure_pmf.expectation (run_steps xs) (\<lambda>\<omega>. of_bool (i \<in> state_\<chi> \<omega>) / state_p \<omega>) = 1\<close>
  (is \<open>?L = _\<close>)
proof -
  have \<open>finite (set_pmf (run_steps xs))\<close>
    using finite_run_state_pmf[where \<rho>=\<open>FinalState xs\<close>] by simp
  note int = integrable_measure_pmf_finite[OF this]
  
  define Mi where \<open>Mi = f ^ len_run_state (FinalState xs)\<close>

  have Mi:\<open>0 < Mi\<close> \<open>Mi \<le> 1\<close>
    unfolding Mi_def using f_range by (auto simp add: power_le_one)
  have \<open>AE \<sigma> in run_state_pmf (FinalState xs). Mi \<le> state_p \<sigma>\<close>
    apply (subst AE_mp[OF state_k_run_state_pmf])
    unfolding Mi_def state_p_def
    using f_range by (auto intro!: power_decreasing)
  then have *: \<open>AE \<sigma> in run_steps xs. Mi \<le> state_p \<sigma>\<close>
    by (metis run_state_pmf.simps(1))
  then have \<open>(\<integral>\<omega>. of_bool (i \<in> state_\<chi> \<omega>) / state_p \<omega> \<partial>run_steps xs) =
    (\<integral>\<tau>. (\<Prod>x\<in>{i}. of_bool (Mi \<le> state_p \<tau>) * (of_bool (x \<in> state_\<chi> \<tau>) / state_p \<tau>)) 
      \<partial>run_state_pmf (FinalState xs))\<close>
    by (auto intro!: integral_cong_AE)
    
  also have \<open>\<dots> \<le> 1 ^ card {i}\<close>
    apply (intro run_steps_preserves_expectation_le'[OF Mi])
    using i unfolding concave_on_iff by auto
  finally have
    le: \<open>?L \<le> 1\<close> by auto

  have concave: \<open>concave_on {0..1 / Mi} ((-) (1 / Mi + 1))\<close>
    unfolding concave_on_iff
    using Mi apply (clarsimp simp add: field_simps)
    by (metis combine_common_factor distrib_right linear mult_1_left)

  have \<open>1 / Mi + 1 - (\<integral>\<omega>. of_bool (i \<in> state_\<chi> \<omega>) / state_p \<omega> \<partial>run_steps xs) =
    (\<integral>\<omega>. 1 / Mi + 1 - of_bool (i \<in> state_\<chi> \<omega>) / state_p \<omega> \<partial>run_steps xs) \<close>
    apply (subst Bochner_Integration.integral_diff)
    using int by auto
  also have \<open>\<dots> = (\<integral>\<tau>. (\<Prod>x\<in>{i}. of_bool (Mi \<le> state_p \<tau>) *
    (1 / Mi + 1 - of_bool (x \<in> state_\<chi> \<tau>) / state_p \<tau>)) \<partial>run_state_pmf (FinalState xs))\<close>
    using * by (auto intro!: integral_cong_AE)
  also have \<open>\<dots> \<le> (1 / Mi + 1 - 1) ^ card {i}\<close>
    apply (intro run_steps_preserves_expectation_le'[OF Mi  concave])
    using i Mi by (auto simp add: field_simps)
  also have \<open>\<dots> = 1 / Mi\<close> by auto
  finally have ge:\<open> -(\<integral>\<sigma>. of_bool (i \<in> state_\<chi> \<sigma>) / state_p \<sigma> \<partial>run_steps xs) \<le> -1\<close> by auto
  show ?thesis using le ge by auto
qed

text \<open>Subsection~\ref{sec:unbiasedness}:\<close>
corollary unbiasedness:
  fixes \<sigma> :: \<open>'a run_state\<close>
  shows \<open>measure_pmf.expectation (run_steps xs) estimate = real (card (set xs))\<close>
    (is \<open>?L = _\<close>)
proof -
  have \<open>finite (set_pmf (run_steps xs))\<close>
    using finite_run_state_pmf[where \<rho>=\<open>FinalState xs\<close>] by simp
  note [simp] = integrable_measure_pmf_finite[OF this]

  have s: \<open>AE \<omega> in run_steps xs. state_\<chi> \<omega> \<subseteq> set xs\<close>
    by (metis run_state_pmf.simps(1) run_state_set.simps(1) state_\<chi>_run_state_pmf)

  have \<open>?L = (\<integral>\<omega>. (\<Sum>i\<in>set xs. of_bool (i \<in> state_\<chi> \<omega>)) / state_p \<omega> \<partial>run_steps xs)\<close>
    unfolding estimate_def state_p_def[symmetric]
    by (auto intro!: integral_cong_AE intro: AE_mp[OF s] simp add: Int_absorb1)

  also have \<open>\<dots> = (\<integral>\<omega>. (\<Sum>i\<in>set xs. of_bool (i \<in> state_\<chi> \<omega>) /state_p \<omega>) \<partial>run_steps xs)\<close>
    by (metis (no_types) sum_divide_distrib)
  also have \<open>\<dots> = (\<Sum>i\<in>set xs. (\<integral>\<omega>. of_bool (i \<in> state_\<chi> \<omega>) /state_p \<omega> \<partial>run_steps xs))\<close>
    by (auto intro: Bochner_Integration.integral_sum)
  also have \<open>\<dots> = (\<Sum>i\<in>set xs. 1)\<close>
    apply (intro sum.cong)
    using run_steps_expectation_sing by auto
  finally show ?thesis by auto
qed

end (* end cvm_algo_abstract *)

end (* end theory *)
