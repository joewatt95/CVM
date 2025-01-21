theory CVM_Algo_Original
  imports   
    CVM_Algo
    Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
    Finite_Fields.Finite_Fields_More_PMF
begin

context
  fixes f :: real
  fixes thresh :: nat
  assumes f_range: \<open>f \<in> {1/2..exp(-1/12)}\<close>
  assumes thresh_gt_0: \<open>thresh > 0\<close>
begin

definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> \<lparr>state_k = 0, state_chi = {}\<rparr>\<close>

definition step_1 :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  "step_1 x \<sigma> = 
    do {
      let k = state_k \<sigma>;
      let chi = state_chi \<sigma>; 

      insert_x_into_chi \<leftarrow> bernoulli_pmf (f ^ k);

      let chi = (chi |>
        if insert_x_into_chi
        then insert x
        else Set.remove x);

      return_spmf (\<sigma>\<lparr>state_chi := chi\<rparr>)
    }"

definition subsample :: \<open>'a set \<Rightarrow> 'a set spmf\<close> where
  \<open>subsample U =
    do {
      keep_in_chi \<leftarrow> prod_pmf U (\<lambda>_. bernoulli_pmf f);
      return_spmf (Set.filter keep_in_chi U)
    }\<close>
 
definition step_2 :: \<open>'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step_2 \<sigma> = 
    do {
      let k = state_k \<sigma>;
      let chi = state_chi \<sigma>;
  
      if card chi = thresh
      then (chi
        |> subsample
        |> map_spmf (\<lambda> chi. \<lparr>state_k = k + 1, state_chi = chi\<rparr>))
      else return_spmf \<sigma>
    }\<close>

definition step_3 :: \<open>'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step_3 \<sigma> = 
    do {
      let chi = state_chi \<sigma>;
  
      if card chi = thresh
      then fail_spmf
      else return_spmf \<sigma>
    }\<close>

definition run_steps :: \<open>'a list \<Rightarrow> 'a state spmf\<close> where
  \<open>run_steps xs \<equiv> foldM_spmf (\<lambda>x \<sigma>. step_1 x \<sigma> \<bind> step_2 \<bind> step_3) xs initial_state\<close>

definition estimate :: "'a state \<Rightarrow> real" where
  "estimate \<sigma> = card (state_chi \<sigma>) / f ^ state_k \<sigma>"

lemma ord_spmf_remove_step3:
  fixes x :: 'a
  shows "ord_spmf (=) (step_1 x \<sigma> \<bind> step_2 \<bind> step_3) (step_1 x \<sigma> \<bind> step_2)"
proof -
  have "ord_spmf (=) (local.step_2 x \<bind> local.step_3) (local.step_2 x)" for x :: "'a state"
  proof -
    have "ord_spmf (=) (local.step_2 x \<bind> local.step_3) (local.step_2 x \<bind> return_spmf)"
      by (intro bind_spmf_mono') (simp_all add:step_3_def)
    thus ?thesis by simp
  qed
  thus ?thesis unfolding bind_spmf_assoc by (intro bind_spmf_mono') simp_all
qed

lemma ord_spmf_run_steps: 
  "ord_spmf (=) (run_steps xs) (foldM_spmf (\<lambda>x \<sigma>. step_1 x \<sigma> \<bind> step_2) xs initial_state)"
  unfolding run_steps_def
proof (induction xs rule:rev_induct)
  case Nil
  then show ?case by simp 
next
  case (snoc x xs)
  show ?case
    unfolding run_steps_def foldM_spmf_snoc
    by (intro ord_spmf_remove_step3 bind_spmf_mono' snoc)
qed

lemma f_range_simple: "f \<in> {1/2..<1}"
proof -
  have "exp (- 1 / 12) < (1::real)" by (approximation 5)
  from dual_order.strict_trans2[OF this]
  show ?thesis using f_range by auto
qed

theorem correctness:
  fixes xs :: \<open>'a list\<close>
  assumes "\<epsilon> \<in> {0<..<1}" "\<delta> \<in> {0<..<1}"
  assumes "real thresh \<ge> 12 / \<epsilon> ^ 2 * ln (6 * real (length xs) / \<delta>)"
  defines "R \<equiv> real (card (set xs))"
  shows "measure (run_steps xs) {\<omega>. fails_or_satisfies (\<lambda>x. \<bar>estimate x - R\<bar> > \<epsilon> * R) \<omega>} \<le> \<delta>"
    (is "?L \<le> ?R")
proof -
  define abs_subsample where 
    "abs_subsample U = map_pmf (\<lambda>\<omega>. Set.filter \<omega> U) (prod_pmf U (\<lambda>_. bernoulli_pmf f))"
    for U :: "'a set"

  interpret abs:cvm_algo_abstract thresh f abs_subsample
    rewrites "abs.estimate = estimate"
  proof -
    show abs:"cvm_algo_abstract thresh f abs_subsample"
    proof (unfold_locales, goal_cases)
      case 1 thus ?case by (rule thresh_gt_0)
    next
      case 2 thus ?case using f_range_simple by auto
    next
      case (3 U x)
      then show ?case unfolding abs_subsample_def by auto
    next
      case (4 g U S)
      hence fin_U: "finite U" using thresh_gt_0 card_gt_0_iff by metis
      note conv = Pi_pmf_subset[OF this 4(1)]

      have "(\<integral>\<omega>. (\<Prod>s\<in>S. g (s \<in> \<omega>)) \<partial>abs_subsample U) = 
        (\<integral>\<omega>. (\<Prod>s\<in>S. g (s \<in> U \<and> \<omega> s)) \<partial>prod_pmf U (\<lambda>_. bernoulli_pmf f))" 
        unfolding abs_subsample_def by (simp cong:prod.cong)
      also have "\<dots> = (\<integral>\<omega>. (\<Prod>s\<in>S. g (s \<in> U \<and> \<omega> s)) \<partial>prod_pmf S (\<lambda>_. bernoulli_pmf f))"
        unfolding conv by simp
      also have "\<dots> = (\<Prod>s\<in>S. (\<integral>\<omega>. g (s \<in> U \<and> \<omega>) \<partial>bernoulli_pmf f))" 
        using fin_U finite_subset[OF 4(1)] 
        by (intro expectation_prod_Pi_pmf integrable_measure_pmf_finite) auto
      also have "\<dots> = (\<Prod>s\<in>S. (\<integral>\<omega>. g \<omega> \<partial>bernoulli_pmf f))" 
        using 4(1) by (intro prod.cong refl) auto
      finally show ?case by simp
    qed
    show "cvm_algo_abstract.estimate f = (estimate :: 'a state \<Rightarrow> real)" 
      unfolding cvm_algo_abstract.estimate_def[OF abs] estimate_def by simp
  qed

  have a: "step_1 \<sigma> x = spmf_of_pmf (abs.step_1 \<sigma> x)" for \<sigma> x
    unfolding step_1_def abs.step_1_def spmf_of_pmf_def by (simp add:map_bind_pmf)

  have b: "step_2 \<sigma> = map_pmf Some (abs.step_2 \<sigma>)" for \<sigma> 
    unfolding step_2_def abs.step_2_def subsample_def abs_subsample_def 
    by (simp add:map_bind_pmf Let_def map_pmf_def[symmetric] map_pmf_comp)

  have c: "abs.initial_state = initial_state" 
    unfolding initial_state_def abs.initial_state_def by simp

  have d: "subsample U = spmf_of_pmf (abs_subsample U)" for U
    unfolding subsample_def abs_subsample_def map_pmf_def[symmetric] 
    by (simp add:spmf_of_pmf_def map_pmf_comp)

  define \<alpha> :: real where "\<alpha> = f ^ thresh"

  have \<alpha>_range: "\<alpha> \<in> {0..1}" 
    using f_range_simple unfolding \<alpha>_def by (auto intro:power_le_one)
  hence [simp]: "\<bar>\<alpha>\<bar> \<le> 1" by auto

  have "(\<integral>x. (if card x = thresh then 1 else 0) \<partial>abs_subsample U) \<le> \<alpha>" (is "?L1 \<le> _")
    if that': "card U = thresh" for U
  proof -
    have fin_U: "finite U" using thresh_gt_0 that card_gt_0_iff by metis

    have "(\<Prod>s\<in>U. of_bool (s \<in> x)::real) = of_bool(card x = thresh)"
      if "x \<in> set_pmf (abs_subsample U)" for x
    proof -
      have x_ran: "x \<subseteq> U" using that unfolding abs_subsample_def by auto

      have "(\<Prod>s\<in>U. of_bool (s \<in> x)::real) = of_bool(x = U)"
        using fin_U x_ran by (induction U rule:finite_induct) auto 
      also have "\<dots> = of_bool (card x = card U)"
        using x_ran fin_U card_subset_eq by (intro arg_cong[where f="of_bool"]) blast
      also have "\<dots> = of_bool (card x = thresh)" using that' by simp
      finally show ?thesis by auto 
    qed
    hence "?L1 = (\<integral>x. (\<Prod>s \<in> U. of_bool(s \<in> x)) \<partial>abs_subsample U)"
      by (intro integral_cong_AE AE_pmfI) simp_all
    also have "\<dots> \<le> (\<Prod>s \<in> U. (\<integral>x. of_bool x \<partial>bernoulli_pmf f))"
      by (intro abs.subsample_inequality that) auto
    also have "\<dots> = f ^ card U" using f_range_simple by simp
    also have "\<dots> = \<alpha>" unfolding \<alpha>_def that by simp
    finally show ?thesis by simp
  qed
  hence e: "pmf (step_2 \<sigma> \<bind> step_3) None \<le> \<alpha>" for \<sigma> :: "'a state" 
    using \<alpha>_range unfolding step_2_def step_3_def d 
    by (simp add:Let_def bind_map_pmf comp_def pmf_bind if_distrib if_distribR cong:if_cong)

  have "pmf (step_1 x \<sigma> \<bind> step_2 \<bind> step_3) None \<le> \<alpha>" for \<sigma> and x :: 'a
  proof-
    have "pmf (step_1 x \<sigma> \<bind> step_2 \<bind> step_3) None \<le> 0 + (\<integral>_. \<alpha> \<partial> measure_spmf (step_1 x \<sigma>))" 
      unfolding bind_spmf_assoc pmf_bind_spmf_None[where p="step_1 x \<sigma>"]
      by (intro add_mono integral_mono_AE measure_spmf.integrable_const_bound[where B="1"] 
          iffD2[OF AE_measure_spmf_iff] ballI e)
         (simp_all add:pmf_le_1 step_1_def map_pmf_def[symmetric] pmf_map vimage_def)
    also have "\<dots> \<le> \<alpha>" using \<alpha>_range by (simp add: mult_left_le_one_le weight_spmf_le_1) 
    finally show ?thesis by simp
  qed
  hence "prob_fail (run_steps xs) \<le> length xs * \<alpha>"
    unfolding run_steps_def by (intro prob_fail_foldM_spmf_le[where P="\<lambda>_. True"]) auto
  also have "\<dots> \<le> \<delta> / 2"
  proof (cases "xs = []")
    case True
    thus ?thesis using assms(2) by auto
  next 
    case False
    have "\<delta> \<le> 6 * 1" using assms(2) by simp
    also have "\<dots> \<le> 6 * real (length xs)"
      using False by (intro mult_mono order.refl) (cases xs, auto) 
    finally have [simp]: " \<delta> \<le> 6 * real (length xs)" by simp
    have "2 * real (length xs) * f ^ thresh \<le> 2 * real (length xs) * exp (-1/12)^thresh"
      using f_range by (intro mult_left_mono power_mono) auto
    also have "\<dots> =  2 * real (length xs) * exp (-real thresh / 12)"
      unfolding exp_of_nat_mult[symmetric] by simp
    also have "\<dots> \<le> 2 * real (length xs) * exp (-(12 / \<epsilon> ^ 2 * ln (6 * real (length xs) / \<delta>))/12)"
      using assms(3) by (intro mult_left_mono iffD2[OF exp_le_cancel_iff] divide_right_mono) auto
    also have "\<dots> = 2 * real (length xs) * exp (-ln (6 * real (length xs) / \<delta>) / \<epsilon>^2 )"
      by auto
    also have "\<dots> \<le> 2 * real (length xs) * exp (-ln (6 * real (length xs) / \<delta>) / 1 )"
      using assms(1,2) False 
      by (intro mult_left_mono iffD2[OF exp_le_cancel_iff] divide_left_mono_neg power_le_one) 
        (auto intro!:ln_ge_zero simp:divide_simps)
    also have "\<dots> = 2 * real (length xs) * exp (ln (inverse (6 * real (length xs) / \<delta>)))"
      using False assms(2) by (subst ln_inverse[symmetric]) auto
    also have "\<dots> = 2 * real (length xs) / (6 * real (length xs) / \<delta>)"
      using assms(1,2) False by (subst exp_ln) auto
    also have "\<dots> = \<delta> / 3" using False assms(2) by auto
    also have "\<dots> \<le> \<delta>" using assms(2) by auto
    finally have "2 * real (length xs) * f^thresh \<le> \<delta>" by simp
    thus ?thesis unfolding \<alpha>_def by simp
  qed
  finally have f:"prob_fail (run_steps xs) \<le> \<delta> / 2" by simp

  have g:"spmf_of_pmf (abs.run_steps xs) = foldM_spmf (\<lambda>x \<sigma>. step_1 x \<sigma> \<bind> step_2) xs initial_state"
    unfolding abs.run_steps_def foldM_spmf_of_pmf_eq(2)[symmetric] 
    unfolding spmf_of_pmf_def map_pmf_def c b a
    by (simp add:bind_assoc_pmf bind_spmf_def bind_return_pmf)

  have "?L \<le> measure (run_steps xs) {None} + 
    measure (measure_spmf (run_steps xs)) {x. \<bar>estimate x - R\<bar> > \<epsilon> * R}"
    unfolding measure_measure_spmf_conv_measure_pmf by (intro pmf_add) (auto split:option.split_asm)
  also have "\<dots> \<le> \<delta> / 2 + measure (measure_spmf (run_steps xs)) {x. \<bar>estimate x - R\<bar> > \<epsilon> * R}"
    unfolding measure_pmf_single by (intro add_mono f order.refl)
  also have "\<dots> \<le> \<delta>/2+measure(measure_spmf (spmf_of_pmf (abs.run_steps xs))) {x. \<bar>estimate x-R\<bar>>\<epsilon>*R}"
    using ord_spmf_eqD_emeasure[OF ord_spmf_run_steps] unfolding measure_spmf.emeasure_eq_measure g
    by (intro add_mono) auto
  also have "\<dots> \<le> \<delta> / 2 + measure (abs.run_steps xs) {x. \<bar>estimate x - R\<bar> > \<epsilon> * R}"
    using measure_spmf_map_pmf_Some spmf_of_pmf_def by auto
  also have "\<dots> \<le> \<delta> / 2 + \<delta> / 2"
    using assms(1-3) unfolding R_def by (intro add_mono abs.correctness) auto
  finally show ?thesis by simp
qed

end

end