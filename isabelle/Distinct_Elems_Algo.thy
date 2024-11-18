section \<open> TODO \<close>
theory Distinct_Elems_Algo

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  CVM.Utils_List
  CVM.Utils_PMF_Basic
  CVM.Utils_PMF_Bernoulli_Binomial
  CVM.Utils_SPMF_FoldM
  CVM.Utils_SPMF_Hoare

begin

record 'a state =
  state_k :: nat
  state_chi :: \<open>'a set\<close>

definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> \<lparr>state_k = 0, state_chi = {}\<rparr>\<close>

definition compute_estimate :: \<open>'a state \<Rightarrow> nat\<close> where
  \<open>compute_estimate state \<equiv> card (state_chi state) * 2 ^ (state_k state)\<close>

context
  fixes
    foldM :: \<open>('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'd \<Rightarrow> 'e state \<Rightarrow> 'f\<close> and
    map :: \<open>('e state \<Rightarrow> nat) \<Rightarrow> 'f \<Rightarrow> 'g\<close> and
    step :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c\<close>
begin

definition run_steps_then_estimate :: \<open>'d \<Rightarrow> 'g\<close> where
  \<open>run_steps_then_estimate \<equiv>
    flip (foldM step) initial_state >>> map compute_estimate\<close>

end

abbreviation
  \<open>run_steps_then_estimate_pmf \<equiv> run_steps_then_estimate foldM_pmf map_pmf\<close>

locale with_threshold =
  fixes threshold :: nat
begin

text
  \<open>The algorithm is defined in the SPMF monad (with None representing failure)\<close>

definition step :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step x state \<equiv> do {
    let k = state_k state;
    let chi = state_chi state;

    insert_x_into_chi \<leftarrow> bernoulli_pmf <| 1 / 2 ^ k;

    let chi = (chi |>
      if insert_x_into_chi
      then insert x
      else Set.remove x);

    if card chi < threshold
    then return_spmf (state\<lparr>state_chi := chi\<rparr>)
    else do {
      keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow>
        prod_pmf chi \<lblot>bernoulli_pmf <| 1 / 2\<rblot>;

      let chi = Set.filter keep_in_chi chi;

      if card chi < threshold
      then return_spmf \<lparr>state_k = k + 1, state_chi = chi\<rparr>
      else fail_spmf }}\<close>

definition estimate_distinct :: \<open>'a list \<Rightarrow> nat spmf\<close> where
  \<open>estimate_distinct \<equiv>
    run_steps_then_estimate foldM_spmf map_spmf step\<close>

lemma
  assumes \<open>threshold > card (set xs)\<close>
  defines
    \<open>P index state \<equiv>
      state_k state = 0 \<and> state_chi state = set (take index xs)\<close>
  shows \<open>\<turnstile>spmf
    \<lbrace>(\<lambda> state. (index, x) \<in> set (List.enumerate 0 xs) \<and> P index state)\<rbrace>
    step x
    \<lbrace>P (Suc index)\<rbrace>\<close>
  using
    assms card_set_take_le_card_set[of "Suc index" xs]
    insert_nth_set_take_eq_set_take_Suc[of index xs]
  by (fastforce
    simp add: hoare_triple_def
      step_def Let_def Set.remove_def Set.filter_def in_set_enumerate_eq
      bind_spmf_of_pmf[symmetric]
    simp del: bind_spmf_of_pmf)

lemma
  assumes \<open>threshold > card (set xs)\<close>
  shows \<open>estimate_distinct xs = return_spmf (card <| set xs)\<close>
proof -
  let ?P = \<open>\<lambda> index state.
    state_k state = 0 \<and> state_chi state = set (take index xs)\<close>

  have \<open>\<turnstile>spmf
    \<lbrace>(\<lambda> state. (index, x) \<in> set (List.enumerate 0 xs) \<and> ?P index state)\<rbrace>
    step x
    \<lbrace>?P (Suc index)\<rbrace>\<close> for index x
    using
      assms card_set_take_le_card_set[of "Suc index" xs]
      insert_nth_set_take_eq_set_take_Suc[of index xs]
    by (fastforce
      simp add: hoare_triple_def
        step_def Let_def Set.remove_def Set.filter_def in_set_enumerate_eq
        bind_spmf_of_pmf[symmetric]
      simp del: bind_spmf_of_pmf)

  then have \<open>\<turnstile>spmf \<lbrace>?P 0\<rbrace> foldM_spmf step xs \<lbrace>?P (length xs)\<rbrace>\<close>
    by (fastforce intro: loop[where offset = 0, simplified])

  then show ?thesis
    apply (auto simp add:
      hoare_triple_def estimate_distinct_def run_steps_then_estimate_def
      initial_state_def)
    sorry
qed

end

locale with_threshold_pos = with_threshold +
  assumes threshold_pos : \<open>threshold > 0\<close>

end