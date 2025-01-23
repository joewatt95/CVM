section \<open>The new Unbiased Algorithm\label{sec:cvm_new}\<close>

text \<open>In this section, we introduce the new algorithm promised in the abstract. 

The key idea is to replace the subsampling step of the original algorithm, which removes each
element of the buffer independently with probability f (see Algorithm~\ref{alg:cvm_new}). 
Instead, we choose a random $nf$-subset of the buffer. 
(This means $f$, $n$ must be choosen, such that $nf$ is integer.)

\begin{algorithm}[h!]
	\caption{New CVM algorithm.\label{alg:cvm_new}}
	\begin{algorithmic}[1]       
  \Require Stream elements $a_1,\ldots,a_l$, $0 < \varepsilon$, $0 < \delta < 1$, $f$ subsampling param.
  \Ensure An estimate $R$, s.t., $\prob \left( | R - |A| | > \varepsilon |A| \right) \leq \delta$ where $A := \{a_1,\ldots,a_l\}.$
  \State $\chi \gets \{\}, p \gets 1, n \geq \ceil{\frac{12}{\varepsilon^2} \ln{(\frac{3l}{\delta})} }$
  \For{$i \gets 1$ to $l$}
    \State $b \getsr \Ber(p)$ \Comment insert $a_i$ with probability $p$ (and remove it otherwise)
    \If{$b$}
      \State $\chi \gets \chi \cup \{a_i\}$
    \Else
      \State $\chi \gets \chi - \{a_i\}$
    \EndIf
    \If{$|\chi| = n$}
      \State $\chi \getsr \mathrm{subsample}(\chi)$ \Comment Choose a random $nf$-subset of $\chi$
      \State $p \gets p f$
    \EndIf
  \EndFor
  \State \Return $\frac{|\chi|}{p}$ \Comment estimate cardinality of $A$
\end{algorithmic}        
\end{algorithm}

The fact that this still preserves the required inequality for the subsampling operation 
(Eq.~\ref{eq:subsample_condition}) is a result following from the negative associativity of
permutation distributions~\cite[Th. 10]{dubhashi1996}.

(See also our formalization of the concept~\cite{Negative_Association-AFP}.)

Because the subsampling step always removes elements unconditionally, the second check, whether
the subsampling succeeded of the original algorithm is not necessary anymore.

This of course improves the space usage of the algorithm, because the fist reduction argument
from Section~\ref{sec:cvm_original} is now obsolete. Moreover the resulting algorithm is now
unbiased, because it is an instance of the abstract algorithm~\ref{sec:cvm_abs}.\<close>

theory CVM_New_Unbiased_Algorithm
  imports
    CVM_Abstract_Algorithm
    Negative_Association.Negative_Association_Permutation_Distributions
begin

unbundle no_vec_syntax

context
  fixes subsample_size :: nat
  fixes thresh :: nat
  assumes subsample_size: \<open>subsample_size < thresh\<close> \<open>2 * subsample_size \<ge> thresh\<close>
begin

text \<open>Line 1:\<close>
definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> \<lparr>state_k = 0, state_\<chi> = {}\<rparr>\<close>

definition f :: real 
  where \<open>f \<equiv> subsample_size / thresh\<close>

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

definition subsample :: \<open>'a set \<Rightarrow> 'a set pmf\<close> where
  \<open>subsample \<chi> = pmf_of_set {S. S \<subseteq> \<chi> \<and> card S = subsample_size}\<close>

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
  \<open>estimate \<sigma> = card (state_\<chi> \<sigma>) / f ^ state_k \<sigma>\<close>

lemma subsample_finite_nonempty:
  assumes \<open>card U = thresh\<close>
  shows
    \<open>{T. T \<subseteq> U \<and> card T = subsample_size} \<noteq> {}\<close> (is \<open>?C \<noteq> {}\<close>)
    \<open>finite {T. T \<subseteq> U \<and> card T = subsample_size}\<close>
    \<open>finite (set_pmf (subsample U))\<close>
proof -
  have fin_U: \<open>finite U\<close> using assms subsample_size 
    by (meson card_gt_0_iff le0 order_le_less_trans order_less_le_trans)
  have a: \<open>card U choose subsample_size > 0\<close>
    using subsample_size assms by (intro zero_less_binomial) auto
  with assms subsample_size have \<open>card ?C > 0\<close>
    using n_subsets[OF fin_U] by simp
  thus \<open>?C \<noteq> {}\<close> \<open>finite ?C\<close> using card_gt_0_iff by blast+
  thus \<open>finite (set_pmf (subsample U))\<close> unfolding subsample_def by auto
qed

(* Lemma 1 *)
lemma int_prod_subsample_eq_prod_int:
  fixes g :: \<open>bool \<Rightarrow> real\<close>
  assumes
    \<open>card U = thresh\<close>
    \<open>S \<subseteq> U\<close> \<open>range g \<subseteq> {0..}\<close>
  shows \<open>(\<integral>\<omega>. (\<Prod>s\<in>S. g(s \<in> \<omega>)) \<partial>subsample U) \<le> (\<Prod>s\<in>S. (\<integral>\<omega>. g \<omega> \<partial>bernoulli_pmf f))\<close> (is \<open>?L \<le> ?R\<close>)
proof -
  define \<eta> where \<open>\<eta> \<equiv> if g True \<ge> g False then Fwd else Rev\<close>

  have fin_U: \<open>finite U\<close> using assms subsample_size 
    by (meson card_gt_0_iff le0 order_le_less_trans order_less_le_trans)

  note subsample_finite_nonempty =
    subsample_finite_nonempty[OF assms(1)]

  note [simp] = integrable_measure_pmf_finite[OF subsample_finite_nonempty(3)]

  let ?C = \<open>{T. T \<subseteq> U \<and> card T = subsample_size}\<close>

  have subssample_size_le_card_U: \<open>subsample_size \<le> card U\<close>
    using subsample_size unfolding assms(1) by simp

  have \<open>measure_pmf.neg_assoc (subsample U) (\<lambda>s \<omega>. (s \<in> \<omega>)) U\<close>
    using subssample_size_le_card_U unfolding subsample_def
    by (intro n_subsets_distribution_neg_assoc fin_U)

  hence na: \<open>measure_pmf.neg_assoc (subsample U) (\<lambda>s \<omega>. (s \<in> \<omega>)) S\<close>
    using measure_pmf.neg_assoc_subset[OF assms(2)] by auto

  have fin_S: \<open>finite S\<close> using assms(2) fin_U finite_subset by auto
  note na_imp_prod_mono = has_int_thatD(2)[OF measure_pmf.neg_assoc_imp_prod_mono[OF fin_S na]]

  have g_borel: \<open>g \<in> borel_measurable borel\<close> by (intro borel_measurable_continuous_onI) simp
  have g_mono_aux: \<open>g x \<le>\<ge>\<^bsub>\<eta>\<^esub> g y\<close> if  \<open>x \<le> y\<close> for x y
    unfolding \<eta>_def using that by simp (smt (verit, best))
  have g_mono: \<open>monotone (\<le>) (\<le>\<ge>\<^bsub>\<eta>\<^esub>) g\<close>
    by (intro monotoneI) (auto simp:dir_le_refl intro!:g_mono_aux)

  have a: \<open>map_pmf (\<lambda>\<omega>. s \<in> \<omega>) (subsample U) = bernoulli_pmf f\<close> if \<open>s \<in> U\<close> for s
  proof -
    have \<open>measure (pmf_of_set ?C) {x. s \<in> x} = real subsample_size / card U\<close>
      by (intro n_subsets_prob subssample_size_le_card_U that fin_U)
    also have \<open>\<dots> = f\<close> unfolding f_def assms(1) by simp
    finally have \<open>measure (pmf_of_set ?C) {x. s \<in> x} = f\<close> by simp
    thus ?thesis by (intro eq_bernoulli_pmfI) (simp add: pmf_map vimage_def subsample_def)
  qed

  have \<open>?L \<le> (\<Prod>s\<in>S. (\<integral>\<omega>. g (s \<in> \<omega>) \<partial>subsample U))\<close>
    by (intro na_imp_prod_mono[OF _ g_mono] g_borel assms(3)) auto
  also have \<open>\<dots> = (\<Prod>s\<in>S. (\<integral>\<omega>. g \<omega> \<partial>map_pmf (\<lambda>\<omega>. s \<in> \<omega>) (subsample U)))\<close> by simp
  also have \<open>\<dots> = ?R\<close> using a assms(2) by (intro prod.cong refl) (metis in_mono)
  finally show ?thesis .
qed

interpretation abs: cvm_algo_abstract thresh f subsample
  rewrites \<open>abs.run_steps = run_steps\<close> and \<open>abs.estimate = estimate\<close>
proof -
  show abs:\<open>cvm_algo_abstract thresh f subsample\<close>
  proof (unfold_locales, goal_cases)
    case 1 thus ?case using subsample_size by auto 
  next
    case 2 thus ?case using subsample_size unfolding f_def by auto
  next
    case (3 U x) thus ?case using subsample_finite_nonempty[OF 3(1)] unfolding subsample_def by simp
  next
    case (4 g U S) thus ?case by (intro int_prod_subsample_eq_prod_int) auto    
  qed
  have a:\<open>cvm_algo_abstract.step_1 f = step_1\<close>
    unfolding cvm_algo_abstract.step_1_def[OF abs] step_1_def by auto
  have b:\<open>cvm_algo_abstract.step_2 thresh subsample = step_2\<close>
    unfolding cvm_algo_abstract.step_2_def[OF abs] step_2_def Let_def by (auto simp:map_pmf_def) 
  have c:\<open>cvm_algo_abstract.initial_state = initial_state\<close>
    unfolding cvm_algo_abstract.initial_state_def[OF abs] initial_state_def by auto
  show \<open>cvm_algo_abstract.run_steps thresh f subsample = run_steps\<close>
    unfolding cvm_algo_abstract.run_steps_def[OF abs] run_steps_def a b c by simp
  show \<open>cvm_algo_abstract.estimate f = estimate\<close>
    unfolding cvm_algo_abstract.estimate_def[OF abs] estimate_def by auto
qed

theorem unbiasedness: 
  \<open>measure_pmf.expectation (run_steps xs) estimate = card (set xs)\<close>
  by (rule abs.unbiasedness)

theorem correctness:
  fixes \<epsilon> \<delta> :: real
  assumes \<open>\<epsilon> \<in> {0<..<1}\<close> \<open>\<delta> \<in> {0<..<1}\<close>
  assumes \<open>real thresh \<ge> 12 / \<epsilon> ^ 2 * ln (3 * real (length xs) / \<delta>)\<close>
  defines \<open>R \<equiv> real (card (set xs))\<close>
  shows \<open>measure (run_steps xs) {\<omega>. \<bar>estimate \<omega> - R\<bar> > \<epsilon> * R } \<le> \<delta>\<close> 
  unfolding R_def by (intro abs.correctness assms)

end

end