theory Distinct_Elems_While

imports
  CVM.Distinct_Elems_Algo
  CVM.Algo_Transforms_No_Fail

begin

context with_threshold
begin

definition fix_state_while :: \<open>'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>fix_state_while \<equiv> loop_spmf.while (\<lambda> state.
    card (state_chi state) = threshold) (\<lambda> state. do {
      let chi = state_chi state;

      keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
        prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi chi;
      let k = state_k state + 1;

      return_spmf \<lparr>state_k = k, state_chi = chi\<rparr>})\<close>

definition step_while :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step_while x state \<equiv> do {
    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ (state_k state);

    let chi = (state
      |> state_chi
      |> if insert_x_into_chi
        then insert x
        else Set.remove x);

    fix_state_while (state\<lparr>state_chi := chi\<rparr>) }\<close>

definition estimate_distinct_while :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_distinct_while \<equiv> run_steps_then_estimate_spmf step_while\<close>
end

context with_threshold_pos
begin

lemma aux :
  fixes state
  defines \<open>chi \<equiv> state_chi state\<close>
  assumes \<open>finite chi\<close> \<open>card chi \<le> threshold\<close>
  shows
    \<open>fix_state_while state = (
      if card (state_chi state) < threshold
      then return_spmf state
      else do {
        keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
          prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

        let chi = Set.filter keep_in_chi chi;
        let k = state_k state + 1;

        fix_state_while \<lparr>state_k = k, state_chi = chi\<rparr> } )\<close>
  unfolding fix_state_while_def Let_def
  apply (subst bind_spmf_of_pmf[symmetric])+
  apply (subst loop_spmf.while.simps)
  apply (subst bind_spmf_assoc)
  using assms by simp

thm SPMF.fundamental_lemma[
  where p = \<open>spmf_of_pmf (step_no_fail x state)\<close>,
  where q = \<open>step_while x state\<close>,
  where A = P, where B = P,
  of
    \<open>\<lambda> state'. card (state_chi state') \<ge> threshold\<close>
    (* \<open>\<lambda> state'. state_k state' > state_k state + 1\<close> *)
]

lemma
  fixes cond g
  assumes
    \<open>\<And> x. lossless_spmf (body x)\<close>
    \<open>\<And> x. lossless_spmf (loop_spmf.while cond body x)\<close>
  shows
    \<open>\<bar>\<P>(x in measure_spmf <| do {x \<leftarrow> p; if cond x then body x else return_spmf x}.
      P x)
      - \<P>(x in measure_spmf <| bind_pmf p <| loop_spmf.while cond body. P x)\<bar>
    \<le> \<P>(x in p. cond x)\<close>
    (is
      \<open>\<bar>\<P>(x in measure_spmf <| bind_pmf _ <| ?if. _)
        - ?prob (loop_spmf.while _ _)\<bar>
      \<le> ?R\<close>)
proof -
  let ?bind_spmf_p = \<open>(>=>) \<lblot>spmf_of_pmf p\<rblot>\<close>

  let ?if_with_flag = \<open>\<lambda> x. pair_spmf (?if x) (return_spmf <| cond x)\<close>

  let ?cond_with_flag = \<open>\<lambda> (x, _). cond x\<close>
  let ?body_with_flag = \<open>\<lambda> (x, _). pair_spmf (body x) (return_spmf True)\<close>
  let ?while_with_flag = \<open>\<lambda> flag x.
    loop_spmf.while ?cond_with_flag ?body_with_flag (x, flag)\<close>

  have while_with_flag_eq :
    \<open>?while_with_flag flag x = (
      if cond x
      then pair_spmf (loop_spmf.while cond body x) (return_spmf True)
      else return_spmf (x, flag))\<close> for flag x
    apply (auto simp add: loop_spmf.while_simps pair_spmf_alt_def)
    apply (intro bind_spmf_cong)
    apply blast

    (* To show that 2 while loops are equal, we appeal to their domain-theoretic
    denotational semantics as least fixed points of transfinite iteration
    sequences, and show, via transfinite induction, that they are upper bounds
    of each other's sequences.

    TODO: Try to derive a relational Hoare logic proof rule that provides a
    simpler API by abstracting away all this domain-theoretic fiddling.
    For reference, see ch5 of http://publications.rwth-aachen.de/record/814578/files/814578.pdf *)
    apply (intro spmf.leq_antisym)
    subgoal for x'
      apply (induction arbitrary: flag x x' rule: loop_spmf.while_fixp_induct[where guard = \<open>\<lambda> (x, _). cond x\<close>])
      by (auto
        intro!: ord_spmf_bind_reflI
        simp add: map_spmf_bind_spmf bind_map_spmf pair_spmf_alt_def loop_spmf.while_simps)

    subgoal for x'
      apply (induction arbitrary: flag x x' rule: loop_spmf.while_fixp_induct[where guard = cond])
      by (auto
        intro: ord_spmf_bind_reflI
        simp add: map_spmf_bind_spmf bind_map_spmf pair_spmf_alt_def loop_spmf.while_simps)
    done

  with assms have \<open>lossless_spmf (?while_with_flag flag x)\<close> for flag x
    by (simp add: pair_spmf_return_spmf2)

  then have \<open>\<turnstile>spmf
    \<lbrace>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrace>
    \<langle>?bind_spmf_p ?if_with_flag | ?bind_spmf_p (?while_with_flag False)\<rangle>
    \<lbrace>(\<lambda> (y, flag) (y', flag'). (flag \<longleftrightarrow> flag') \<and> (\<not> flag \<longrightarrow> y = y'))\<rbrace>\<close>
    apply (intro Utils_SPMF_Relational.seq'[where S = \<open>(=)\<close>])
    apply (simp add: Utils_SPMF_Relational.relational_hoare_triple_def spmf_rel_eq)
    unfolding pair_spmf_alt_def
    apply (simp add: if_distrib if_distribR loop_spmf.while.simps)
    apply (intro Utils_SPMF_Relational.if_then_else)
    apply blast
    apply (intro Utils_SPMF_Relational.seq'[where S = \<open>\<lambda> x (x', flag). flag\<close>])
    apply (simp add: Utils_SPMF_Relational.relational_hoare_triple_def)
    apply (metis (no_types, lifting) bind_return_spmf case_prodI option.rel_inject(2) rel_pmf_return_pmfI rel_spmf_bind_reflI)
    subgoal
      apply (subst Utils_SPMF_Relational.skip_left')
      apply (smt (verit, del_insts) case_prodE loop_spmf.while.simps lossless_return_spmf split_conv)
      by (auto
        intro!:
          Utils_SPMF_Hoare.while Utils_SPMF_Hoare.seq'
          Utils_SPMF_Hoare.postcond_true
        simp add: case_prod_beta')
    by (simp add: Utils_SPMF_Relational.relational_hoare_triple_def)

  with SPMF.fundamental_lemma[
    where p = \<open>p \<bind> ?if_with_flag\<close>,
    where q = \<open>p \<bind> (?while_with_flag False)\<close>,
    where A = \<open>P <<< fst\<close>, where B = \<open>P <<< fst\<close>,
    of snd snd]
  have
    \<open>\<bar>\<P>(x in measure_spmf <| p \<bind> ?if_with_flag. P (fst x))
      - \<P>(x in measure_spmf <| p \<bind> (?while_with_flag False). P (fst x))\<bar>
    \<le> \<P>(x in measure_spmf <| p \<bind> ?if_with_flag. snd x)\<close>
    by (fastforce
      intro: rel_spmf_mono
      simp add:
        Utils_SPMF_Relational.relational_hoare_triple_def space_measure_spmf)

  also have \<open>\<dots> \<le> ?R\<close>
  proof -
    from assms have \<open>\<turnstile>spmf
      \<lbrace>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrace>
      \<langle>?bind_spmf_p ?if_with_flag | ?bind_spmf_p return_spmf\<rangle>
      \<lbrace>(\<lambda> (_, flag) x'. flag \<longleftrightarrow> cond x')\<rbrace>\<close>
      unfolding pair_spmf_alt_def
      apply (intro Utils_SPMF_Relational.seq[where S = \<open>(=)\<close>])
      apply (simp add: Utils_SPMF_Relational.relational_hoare_triple_def spmf_rel_eq) 
      by (auto intro: Utils_SPMF_Hoare.seq' Utils_SPMF_Hoare.postcond_true)

    then show ?thesis
      by (auto
        dest: rel_spmf_measureD[where A = \<open>{x. snd x}\<close>]
        simp add: Utils_SPMF_Relational.relational_hoare_triple_def space_measure_spmf)
  qed

  finally show ?thesis
    apply (simp add: space_measure_spmf while_with_flag_eq)
    using measure_map_spmf[of fst, where A = \<open>{x. P x}\<close>, simplified vimage_def, simplified]
    by (smt (verit, best) bind_pmf_cong loop_spmf.while_simps(2) map_bind_pmf map_fst_pair_spmf pair_spmf_return_spmf scale_spmf_eq_same weight_return_spmf)
qed

lemma
  fixes cond g and f f' :: \<open>'a \<Rightarrow> 'a spmf\<close>
  assumes [simp] :
    \<open>\<And> x. lossless_spmf (f x)\<close>
    \<open>\<And> x. lossless_spmf (f' x)\<close>
    \<open>\<And> x. lossless_spmf (g x)\<close>
  defines [simp] : \<open>go \<equiv> \<lambda> f x. if cond x then f x else g x\<close>
  shows
    \<open>\<bar>\<P>(x in measure_spmf <| bind_pmf p <| go f. P x)
      - \<P>(x in measure_spmf <| bind_pmf p <| go f'. P x)\<bar>
    \<le> \<P>(x in p. cond x)\<close>
proof -
  let ?kleisli_spmf_p = \<open>(>=>) \<lblot>spmf_of_pmf p\<rblot>\<close>

  let ?go_with_flag = \<open>\<lambda> f x.
    if cond x
    then pair_spmf (f x) (return_spmf True)
    else pair_spmf (g x) (return_spmf False)\<close>

  have \<open>\<turnstile>spmf
    \<lbrace>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrace>
    \<langle>?kleisli_spmf_p (?go_with_flag f) | ?kleisli_spmf_p (?go_with_flag f')\<rangle>
    \<lbrace>(\<lambda> (y, flag) (y', flag'). (flag \<longleftrightarrow> flag') \<and> (\<not> flag \<longrightarrow> y = y'))\<rbrace>\<close>
    unfolding pair_spmf_alt_def
    apply (subst bind_commute_spmf)
    apply (intro
      Utils_SPMF_Relational.seq'[where S = \<open>(=)\<close>]
      Utils_SPMF_Relational.if_then_else
      Utils_SPMF_Relational.seq'[where S = \<open>curry fst\<close>])
    by (auto intro: Utils_SPMF_Hoare.seq' Utils_SPMF_Hoare.hoare_tripleI)

  with SPMF.fundamental_lemma[
    where p = \<open>p \<bind> ?go_with_flag f\<close>, where q = \<open>p \<bind> ?go_with_flag f'\<close>,
    where A = \<open>P <<< fst\<close>, where B = \<open>P <<< fst\<close>,
    of snd snd]
  have
    \<open>\<bar>\<P>(x in measure_spmf <| p \<bind> ?go_with_flag f. P (fst x))
      - \<P>(x in measure_spmf <| p \<bind> ?go_with_flag f'. P (fst x))\<bar>
    \<le> \<P>(x in measure_spmf <| p \<bind> ?go_with_flag f. snd x)\<close>
    by (fastforce
      intro: rel_spmf_mono
      simp add:
        Utils_SPMF_Relational.relational_hoare_triple_def space_measure_spmf)

  also have \<open>\<dots> \<le> \<P>(x in p. cond x)\<close>
  proof -
    have \<open>\<turnstile>spmf
      \<lbrace>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrace>
      \<langle>?kleisli_spmf_p (?go_with_flag f) | ?kleisli_spmf_p return_spmf\<rangle>
      \<lbrace>(\<lambda> (_, flag) x'. flag \<longleftrightarrow> cond x')\<rbrace>\<close>
      unfolding pair_spmf_alt_def
      by (fastforce intro:
        Utils_SPMF_Relational.seq[where S = \<open>(=)\<close>]
        Utils_SPMF_Hoare.if_then_else Utils_SPMF_Hoare.seq'
        Utils_SPMF_Hoare.postcond_true)

    then show ?thesis
      by (auto
        dest: rel_spmf_measureD[where A = \<open>{x. snd x}\<close>]
        simp add: Utils_SPMF_Relational.relational_hoare_triple_def space_measure_spmf)
  qed

  finally show ?thesis
    apply (simp add:
      space_measure_spmf map_bind_pmf if_distrib
      measure_map_spmf[of fst, where A = \<open>{x. P x}\<close>, simplified vimage_def, simplified, symmetric])
    unfolding map_fst_pair_spmf map_snd_pair_spmf weight_return_spmf scale_spmf_1 .
qed

(* lemma
  assumes \<open>state ok\<close>
  shows \<open>prob_fail (step_while x state) \<le> prob_fail (step x state)\<close>
proof -
  have \<open>\<turnstile>pmf
    \<lbrakk>(\<lambda> state state'. state = state' \<and> (state ok))\<rbrakk>
    \<langle>step x | step_while x\<rangle>
    \<lbrakk>ord_option (=)\<rbrakk>\<close>
    (is \<open>\<turnstile>pmf \<lbrakk>?R\<rbrakk> \<langle>_ | _ \<rangle> \<lbrakk>_\<rbrakk>\<close>)
    unfolding
      step_def step_while_def well_formed_state_def Let_def
      Set.filter_def Set.remove_def 
    apply (rule Utils_PMF_Relational.seq'[where S = \<open>(=)\<close>])
    apply (simp add: Utils_PMF_Relational.relational_hoare_triple_def pmf.rel_refl)
    apply (subst aux)
    apply (simp_all add: card_insert_if le_diff_conv)
    by (fastforce
      intro: Utils_PMF_Relational.if_then_else Utils_PMF_Relational.seq'[where S = \<open>(=)\<close>]
      simp add: aux Set.filter_def fail_spmf_def Utils_PMF_Relational.relational_hoare_triple_def pmf.rel_refl)

  with assms show ?thesis
    by (blast intro: prob_fail_le_of_relational_hoare_triple)
qed *)

end

end