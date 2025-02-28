section \<open>CVM error bounds\<close>

text
  \<open>This section formalises the proofs of the bounds of
  (1): $\text{Pr}[\text{Error}_2 \cap \overline{\text{Bad}_2}]$
  and (2): $\text{Pr}[\text{Bad}_2]$
  as in \cite{cvm_2023}.
  
  These bounds are established by the following main results:
  \begin{itemize}
    \item \texttt{prob\_eager\_algo\_k\_le\_l\_and\_est\_out\_of\_range\_le}
    formalises the proof for (1)
    \item \texttt{prob\_eager\_algo\_k\_gt\_l\_le}
    foramlises the proof for (2)
  \end{itemize}
  
  Note that our results are more generic than those in \cite{cvm_2023} as we
  allow for a range of values for the threshold (which include the one used there).\<close>

theory CVM_Error_Bounds

imports
  "HOL-Decision_Procs.Approximation"
  CVM_Algo_Nondet_Binomial
  Utils_Concentration_Ineqs

begin

locale cvm_error_bounds = cvm_algo + fixes
  r l :: nat and
  \<epsilon> :: real and
  xs :: \<open>'a list\<close>
begin

abbreviation
  \<open>run_with_bernoulli_matrix \<equiv> \<lambda> g.
    map_pmf (g xs) (bernoulli_matrix (length xs) (length xs) f)\<close>

subsection \<open>Definitions of bounds\<close>

text
  \<open>Bound for the case when $k \le l$, ie $\text{Pr}[\text{Bad}_2]$ of
  \cite{cvm_2023}\<close>

definition
  \<open>prob_k_le_l_and_est_out_of_range_bound \<equiv>
    4 * exp (-\<epsilon>\<^sup>2 * threshold / (4 * real r * (1 + \<epsilon> / 3)))\<close>

text
  \<open>Bound for the case when $k > l$, ie
  $\text{Pr}[\text{Error}_2 \cap \overline{\text{Bad}_2}] of \cite{cvm_2023}$\<close>

definition
  \<open>prob_k_gt_l_bound \<equiv>
    real (length xs) *
    exp (-3 * real threshold * (r - 1)\<^sup>2 / (5 * r + 2 * r\<^sup>2))\<close>

end

locale cvm_error_bounds_assms = cvm_error_bounds + cvm_algo_assms
begin

subsection \<open>Bounding the $k$ <= $l$ case\<close>

context
  assumes
    \<open>threshold \<ge> r\<close>
    \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close>
begin

lemma l_le_length_xs :
  \<open>l \<le> length xs\<close>
proof -
  from \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close>
  (* Isabelle2025:
  have \<open>l \<le> floor_log (2 * r * card (set xs) div threshold)\<close>
    by (metis floor_log_le_iff less_eq_div_iff_mult_less_eq floor_log_power threshold) *)
  have \<open>l \<le> Discrete.log (2 * r * card (set xs) div threshold)\<close>
    by (metis log_le_iff less_eq_div_iff_mult_less_eq log_exp threshold)

  also from \<open>threshold \<ge> r\<close> threshold
  (* Isabelle2025:
  have \<open>\<dots> \<le> floor_log (2 * length xs)\<close>
    by (smt (verit, del_insts) Groups.mult_ac(2,3) card_length div_mult_self1_is_m floor_log_le_iff less_eq_div_iff_mult_less_eq mult_le_mono nat_le_linear
      verit_la_disequality) *)
  have \<open>\<dots> \<le> Discrete.log (2 * length xs)\<close>
    by (smt (verit, del_insts) Groups.mult_ac(2,3) card_length div_mult_self1_is_m log_le_iff less_eq_div_iff_mult_less_eq mult_le_mono nat_le_linear
      verit_la_disequality)

  also have \<open>\<dots> \<le> length xs\<close>
    (* Isabelle2025: by (metis floor_log_le_iff less_exp floor_log_exp2_le floor_log_power floor_log_twice nat_0_less_mult_iff not_le not_less_eq_eq order_class.order_eq_iff self_le_ge2_pow zero_le) *)
    by (metis log_le_iff less_exp log_exp2_le log_exp log_twice nat_0_less_mult_iff not_le not_less_eq_eq order_class.order_eq_iff self_le_ge2_pow zero_le)

  finally show ?thesis .
qed

lemma r_pos :
  \<open>r > 0\<close>
  using \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close> threshold power_eq_0_iff
  by fastforce

text
  \<open>Main result for the $\text{Pr}[\text{Error}_2 \cap \overline{\text{Bad}_2}]$ bound
  as in \cite{cvm_2023}.\<close>

theorem prob_eager_algo_k_le_l_and_est_out_of_range_le :
  assumes \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close>
  shows
    \<open>\<P>(state in run_with_bernoulli_matrix <|
        run_reader <<< flip run_steps_eager initial_state.
      state_k state \<le> l \<and> compute_estimate state >[\<epsilon>] card (set xs))
    \<le> prob_k_le_l_and_est_out_of_range_bound\<close>
    (is \<open>?L (\<le>) l \<le> _\<close>)
proof (cases xs)
  case Nil
  with \<open>\<epsilon> > 0\<close> show ?thesis
    unfolding
      compute_estimate_def prob_k_le_l_and_est_out_of_range_bound_def
      initial_state_def
    by simp
next
  case (Cons _ _)

  let ?exp_bound =
    \<open>exp (-\<epsilon>\<^sup>2 * threshold / (4 * real r * (1 + \<epsilon> / 3)))\<close>
  let ?exp_term = \<open>\<lambda> k.
    exp (- (real (card (set xs)) * f ^ k * \<epsilon>\<^sup>2 / (2 + 2 * \<epsilon> / 3)))\<close>
  let ?binom_mean = \<open>\<lambda> k. f ^ k * real (card <| set xs)\<close>

  text \<open>Apply subadditivity.\<close>
  have \<open>?L (\<le>) l \<le> (\<Sum> k \<le> l. ?L (=) k)\<close>
  proof -
    have [simp] :
      \<open>{x. f x \<le> l \<and> P x} = (
        \<Union> k \<le> l. {x. f x = k \<and> P x})\<close> for f :: \<open>'b \<Rightarrow> nat\<close> and P by auto
    show ?thesis
      by (auto
        intro: measure_pmf.finite_measure_subadditive_finite
        simp add: vimage_def)
  qed

  text \<open>Transform to binomial distribution and weaken $>$ to $\ge$.\<close>
  also have \<open>\<dots> \<le> (
    \<Sum> k \<le> l.
      \<P>(estimate in binomial_pmf (card <| set xs) <| f ^ k.
        \<bar>real estimate - ?binom_mean k\<bar> \<ge> \<epsilon> * ?binom_mean k))\<close>
    (is \<open>(\<Sum> k \<le> _. ?L k) \<le> (\<Sum> k \<le> _. ?R k)\<close>)
  proof (intro sum_mono, unfold atMost_iff)
    fix k assume \<open>k \<le> l\<close>
    with
      \<open>\<epsilon> > 0\<close> l_le_length_xs
      prob_eager_algo_le_binomial[where
        k = k and xs = xs and m = \<open>length xs\<close> and n = \<open>length xs\<close> and
        P = \<open>\<lambda> est. est / f ^ k >[\<epsilon>] card (set xs)\<close>]
    show \<open>?L k \<le> ?R k\<close>
      unfolding compute_estimate_def
      apply (simp add: Let_def field_simps)
      by (smt (verit, ccfv_threshold) mem_Collect_eq mult.commute pmf_mono)
  qed

  text \<open>Apply multiplicative two-sided Chernoff bound to each term.\<close>
  also have
    \<open>\<dots> \<le> (\<Sum> k \<le> l. 2 * ?exp_term k)\<close> (is \<open>(\<Sum> k \<le> _. ?L k) \<le> (\<Sum> k \<le> _. ?R k)\<close>)
  proof (intro sum_mono)
    fix k
    from \<open>\<epsilon> > 0\<close>
      binomial_distribution.chernoff_prob_abs_ge[
        where n = \<open>card <| set xs\<close> and p = \<open>f ^ k\<close> and \<delta> = \<epsilon>]
    show \<open>?L k \<le> ?R k\<close>
      unfolding binomial_distribution_def
      by (simp add: power_le_one algebra_simps)
  qed

  text
    \<open>In preparation to bound via a geometric series, we first transform each
    term to be of the form ${2 * \text{exp\_term}(l)} ^ {2 ^ r}$ so that we can
    later pull out a factor of $2 * \text{exp\_term}(l)$ from each term.

    Note that $\text{exp\_term}(l) < 1$ and that this is important for obtaining
    a tight bound later on.\<close>
  also from \<open>\<epsilon> > 0\<close> have
    \<open>\<dots> = (\<Sum> k \<le> l. 2 * ((?exp_term l) powr (1 / f ^ (l - k))))\<close>
    (is \<open>_ = (\<Sum> k \<le> _. ?g k)\<close>)
    apply (intro sum.cong refl)
    apply (simp add: exp_powr_real field_split_simps Cons)
    unfolding Multiseries_Expansion.intyness_simps
    by (smt (verit, best) Multiseries_Expansion.intyness_simps(5) linordered_semidom_class.add_diff_inverse more_arith_simps(11) mult.commute mult_pos_pos not_less of_nat_0_less_iff power_add
      rel_simps(51) zero_less_power)

  text
    \<open>Now we do the following:
    \begin{enumerate}
      \item Reverse the sum from $l \longrightarrow 0$, to $0 \longrightarrow l$

      \item Reindex the sum to be taken over exponents $r$ of the form $2 ^ k$
       instead of being over all $k$.

      \item Pull out a factor of $2 * \text{exp\_term}(l)$ from each term.
    \end{enumerate}\<close>
  also from assms have
    \<open>\<dots> = 2 * ?exp_term l * (\<Sum> r \<in> power 2 ` {.. l}. ?exp_term l ^ (r - 1))\<close>
    unfolding
      sum_distrib_left
      sum.atLeastAtMost_rev[of ?g 0 l, simplified atLeast0AtMost]
    (* Isabelle2025:
    apply (intro sum.reindex_bij_witness[of _ floor_log \<open>(^) 2\<close>])
      by (auto
        simp flip: exp_of_nat_mult exp_add
        simp add: exp_powr_real field_split_simps) *)
    apply (intro sum.reindex_bij_witness[of _ Discrete.log \<open>(^) 2\<close>])
      by (auto
        simp flip: exp_of_nat_mult exp_add
        simp add: exp_powr_real field_split_simps of_nat_diff_real)

  text
    \<open>Upper bound by a partial geometric series, taken over all $r \in \mathbb{N}$
    up to $2 ^ l$.\<close>
  also have \<open>\<dots> \<le> 2 * ?exp_term l * (\<Sum> r \<le> 2 ^ l - 1. ?exp_term l ^ r)\<close>
    apply (intro mult_mono sum_le_included[where i = Suc] sum_nonneg)
      apply simp_all
      by (meson Suc_pred atMost_iff diff_le_mono less_eq_real_def nat_zero_less_power_iff pos2 power_increasing rel_simps(25))

  text \<open>Upper bound by infinite geometric series.\<close>
  also have \<open>\<dots> \<le> 2 * ?exp_term l * (1 / (1 - ?exp_term l))\<close>
  proof -
    from Cons \<open>\<epsilon> > 0\<close> have \<open>?exp_term l < 1\<close> using order_less_le by fastforce
    with \<open>\<epsilon> > 0\<close> show ?thesis
      by (auto intro: sum_le_suminf simp flip: suminf_geometric)
  qed

  also have \<open>\<dots> \<le> 4 * ?exp_bound\<close>
  proof -
    have
      \<open>2 * x / (1 - x) \<le> 4 * y\<close>
      if \<open>0 \<le> x\<close> \<open>x \<le> y\<close> \<open>y \<le> 1 / 2\<close> for x y :: real
      using that by sos

    then show ?thesis when
      \<open>?exp_term l \<le> ?exp_bound\<close> (is ?thesis_0)
      \<open>?exp_bound \<le> 1 / 2\<close> (is ?thesis_1) 
      using that by simp_all

    from \<open>2 ^ l * threshold \<le> 2 * r * card (set xs)\<close> \<open>\<epsilon> > 0\<close> r_pos threshold
    show ?thesis_0
      by (auto
        intro: add_mono
        simp add: field_split_simps pos_add_strict approximation_preproc_nat(13))

    from \<open>0 < \<epsilon>\<close> \<open>\<epsilon> \<le> 1\<close> have
      \<open>4 * r * (1 + 1 * \<epsilon> / 3) \<le> \<epsilon>\<^sup>2 * threshold\<close>
      if \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close> \<open>r \<ge> 1\<close> for r threshold
      using that by sos

    with \<open>\<epsilon>\<^sup>2 * threshold \<ge> 6 * r\<close> \<open>\<epsilon> > 0\<close> r_pos
    have \<open>?exp_bound \<le> exp (- 1)\<close> by simp
    also have \<open>\<dots> \<le> 1 / 2\<close> by (approximation 0)
    finally show ?thesis_1 .
  qed

  finally show ?thesis unfolding prob_k_le_l_and_est_out_of_range_bound_def .
qed

end

subsection \<open>Bounding the $k > l$ case\<close>

text
  \<open>This next helper Lemma says that if $k > l$ after running the eager
  algorithm, then it must have been the case that at some point during the
  execution of the algorithm, we reach a state where after running
  \texttt{step\_1\_eager}, $k = l$ and $\chi$ hits the threshold.\<close>

lemma exists_index_threshold_exceeded_of_k_exceeds :
  assumes \<open>state_k (run_reader (run_steps_eager xs initial_state) \<phi>) > l\<close>
  shows
    \<open>\<exists> i < length xs.
      state_k (run_reader (run_steps_eager_then_step_1 i xs) \<phi>) = l \<and>
      card (state_chi <| run_reader (run_steps_eager_then_step_1 i xs) \<phi>)
      \<ge> threshold\<close>
    (is \<open>?thesis' xs\<close>)
using assms proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by (simp add: initial_state_def)
next
  case (snoc x xs)
  show ?case
  proof (rule ccontr)
    let ?xs' = \<open>xs @ [x]\<close>
    assume \<open>\<not> ?thesis' ?xs'\<close>
    then have not_thesis' : \<open>\<And> i.
      \<lbrakk>i < length ?xs';
        state_k (run_reader (run_steps_eager_then_step_1 i ?xs') \<phi>) = l\<rbrakk> \<Longrightarrow>
      card (state_chi <| run_reader (run_steps_eager_then_step_1 i ?xs') \<phi>)
      < threshold\<close>
      (is \<open>PROP ?not_thesis' (_ :: _ list)\<close>) by (simp add: not_le)

    then have \<open>PROP ?not_thesis' _ xs\<close>
      unfolding step_1_eager_def'
      apply simp
      by (smt (verit, best) less_SucI nth_append)

    with snoc.IH
    have \<open>state_k (run_reader (run_steps_eager xs initial_state) \<phi>) \<le> l\<close>
      (is \<open>?P xs (\<le>)\<close>) using not_le by blast

    then show False
    proof (unfold le_less, elim disjE)
      assume \<open>?P xs (<)\<close>

      then have \<open>?P (xs @ [x]) (\<le>)\<close>
        unfolding run_steps_eager_snoc
        unfolding step_eager_def step_1_eager_def' step_2_eager_def'
        by simp

      with snoc.prems show False by simp
    next
      assume \<open>?P xs (=)\<close>

      with snoc.prems have
        \<open>card (state_chi <|
          run_reader (run_steps_eager_then_step_1 (length xs) ?xs') \<phi>)
        = threshold\<close>
        (is \<open>?Q (=)\<close>)
        unfolding take_length_eq_self run_steps_eager_snoc
        unfolding step_eager_def step_1_eager_def' step_2_eager_def'
        by (auto split: if_splits)

      moreover from \<open>?P xs (=)\<close> not_thesis'
      have \<open>?Q (<)\<close>
        unfolding run_steps_eager_snoc step_1_eager_def'
        apply simp
        by (smt (verit, ccfv_threshold) append.right_neutral lessI nth_append_length take_length_eq_self)

      ultimately show False by simp
    qed
  qed
qed

lemma
  defines [simp] : \<open>state_k_bounded \<equiv> \<lambda> idx \<phi> state. state_k state \<le> idx\<close>
  shows 
    initial_state_k_bounded :
      \<open>state_k_bounded idx \<phi> initial_state\<close> (is \<open>PROP ?thesis_0\<close>) and

    step_eager_k_bounded : \<open>\<And> idx.
      idx < length xs \<Longrightarrow> \<turnstile>rd
        \<lbrakk>state_k_bounded idx\<rbrakk>
        step_eager xs idx
        \<lbrakk>state_k_bounded (Suc idx)\<rbrakk>\<close> (is \<open>PROP ?thesis_1\<close>) and

    run_steps_eager_k_bounded : \<open>\<turnstile>rd
      \<lbrakk>state_k_bounded 0\<rbrakk>
      (run_steps_eager xs)
      \<lbrakk>state_k_bounded (length xs)\<rbrakk>\<close> (is \<open>PROP ?thesis_2\<close>)
proof -
  show \<open>PROP ?thesis_0\<close> by (simp add: initial_state_def)
  show \<open>PROP ?thesis_1\<close>
    unfolding step_eager_def step_1_eager_def' step_2_eager_def' by simp
  with hoare_foldM_indexed[where P = state_k_bounded and f = \<open>step_eager xs\<close>]
  show \<open>PROP ?thesis_2\<close>
    apply (simp add: in_set_enumerate_eq)
    by (metis (no_types, lifting) One_nat_def le_simps(2) length_upt not_less_eq nth_upt plus_1_eq_Suc semiring_norm(163) verit_minus_simplify(2))
qed

text \<open>Main result for the $\text{Pr}[\text{Bad}_2]$ bound as in \cite{cvm_2023}.\<close>

theorem prob_eager_algo_k_gt_l_le :
  assumes \<open>r \<ge> 2\<close> \<open>2 ^ l * threshold \<ge> r * card (set xs)\<close>
  shows
    \<open>\<P>(state in
      run_with_bernoulli_matrix <| run_reader <<< flip run_steps_eager initial_state.
      state_k state > l)
    \<le> prob_k_gt_l_bound\<close>
    (is \<open>?L \<le> _\<close>)
proof (cases \<open>l > length xs\<close>)
  case True
  with initial_state_k_bounded run_steps_eager_k_bounded
  have \<open>?L = 0\<close>
    apply (simp add: measure_pmf.prob_eq_0 AE_measure_pmf_iff not_less)
    by (meson basic_trans_rules(23) bot_nat_0.extremum_unique leD nat_le_linear)
  then show ?thesis by (simp add: prob_k_gt_l_bound_def) 
next
  case False
  then have \<open>l \<le> length xs\<close> by simp

  let ?exp_term = \<open>exp (-3 * real threshold * (r - 1)\<^sup>2 / (5 * r + 2 * r\<^sup>2))\<close>

  from exists_index_threshold_exceeded_of_k_exceeds
  have \<open>?L \<le>
    \<P>(\<phi> in bernoulli_matrix (length xs) (length xs) f.
      \<exists> i < length xs. (
        let state = run_reader (run_steps_eager_then_step_1 i xs) \<phi>
        in state_k state = l \<and> card (state_chi state) \<ge> threshold))\<close>
    by (auto intro: pmf_mono simp add: Let_def)

  text \<open>Union bound\<close>
  also have \<open>\<dots> \<le> (
    \<Sum> i < length xs.
      \<P>(\<phi> in bernoulli_matrix (length xs) (length xs) f.
        let state = run_reader (run_steps_eager_then_step_1 i xs) \<phi>
        in state_k state = l \<and> card (state_chi state) \<ge> threshold))\<close>
    proof -
      have [simp] : \<open>{\<omega>. \<exists> i < n. P i \<omega>} = (\<Union> i < n. {\<omega>. P i \<omega>})\<close>
        for n and P :: \<open>nat \<Rightarrow> 'b \<Rightarrow> bool\<close> by blast
      show ?thesis by (auto intro: measure_pmf.finite_measure_subadditive_finite)
    qed

  also have \<open>\<dots> \<le> (
    \<Sum> i < length xs.
      \<P>(estimate in binomial_pmf (card <| set <| take (Suc i) xs) (1 / 2 ^ l).
        real estimate \<ge> real threshold))\<close>
    (is \<open>_ \<le> (\<Sum> i < _. ?prob i)\<close>)
    using
      prob_eager_algo_then_step_1_le_binomial[where xs = xs] \<open>l \<le> length xs\<close>
    by (auto intro: sum_mono simp add: field_simps)

  also have \<open>\<dots> \<le> real (length xs) * ?exp_term\<close>
  proof (intro sum_bounded_above[where A = \<open>{..< length xs}\<close>, simplified card_lessThan])
    fix i show \<open>?prob i \<le> ?exp_term\<close>
    proof (cases xs)
      case Nil
      then show ?thesis
        by (simp add: binomial_pmf_0 threshold initial_state_def)
    next
      define p :: real and n \<mu> \<alpha> where
        [simp] : \<open>p \<equiv> 1 / 2 ^ l\<close> and
        \<open>n \<equiv> card (set <| take (Suc i) xs)\<close> and
        [simp] : \<open>\<mu> \<equiv> n * p\<close> and
        \<open>\<alpha> \<equiv> threshold / \<mu>\<close>

      case (Cons _ _)
      then have \<open>n \<ge> 1\<close> by (simp add: n_def leI)
      with \<open>2 ^ l * threshold \<ge> r * (card <| set xs)\<close>
      have \<open>\<alpha> \<ge> r\<close> and [simp] : \<open>threshold = \<alpha> * \<mu>\<close>
        apply (simp_all add: \<alpha>_def n_def field_simps Cons)
        by (metis (full_types) List.finite_set Multiseries_Expansion.intyness_simps(2) card_mono le_trans list.set(2) local.Cons mult_le_mono2 of_nat_le_iff of_nat_numeral of_nat_power
          push_bit_nat_def set_take_subset take_Suc_Cons)

      text \<open>Apply multiplicative upper-tail Chernoff bound\<close>
      with binomial_distribution.chernoff_prob_ge[
        of p \<open>\<alpha> - 1\<close> n, simplified binomial_distribution_def]
      have \<open>?prob i \<le> exp (- real n * p * (\<alpha> - 1)\<^sup>2 / (2 + 2 * (\<alpha> - 1) / 3))\<close>
        using \<open>r \<ge> 2\<close> by (simp add: n_def algebra_simps)

      also have \<open>\<dots> \<le> ?exp_term\<close>
      proof -
        have
          \<open>27*\<alpha>\<^sup>2*r - 24*\<alpha>*r\<^sup>2 - 6*\<alpha>*r - 6*\<alpha>\<^sup>2 + 6*r\<^sup>2 - 12*\<alpha> + 15*r \<ge> 0\<close>
          (is \<open>?expr r \<ge> 0\<close>)
          if \<open>\<alpha> \<ge> r\<close> \<open>r \<ge> 2\<close> for r :: real using that by sos

        with \<open>\<alpha> \<ge> r\<close> \<open>r \<ge> 2\<close> have
          \<open>2 ^ l * n * ?expr r \<ge> 0\<close>
          \<open>4 * 2 ^ l + \<alpha> * (2 * 2 ^ l) > 0\<close>
          by (simp_all add: pos_add_strict)

        with \<open>n \<ge> 1\<close> \<open>\<alpha> \<ge> r\<close> \<open>r \<ge> 2\<close> show ?thesis
          by (auto simp add:
            field_split_simps power_numeral_reduce add_increasing less_le_not_le
            Multiseries_Expansion.of_nat_diff_real)
      qed

      finally show ?thesis .
    qed
  qed

  finally show ?thesis unfolding prob_k_gt_l_bound_def .
qed

end

end