section \<open>CVM algorithm definition\<close>

text
  \<open>Here, we define the CVM algorithm, ie algorithm 1 from \cite{cvm_2023}.
  
  For this, we define the notion of a \texttt{state} record, which tracks the
  $k$ and $\chi$ values across the loop iterations, via the \texttt{state\_k}
  and \texttt{state\_chi} fields.

  The loop in the CVM algorithm is then modelled as a monadic fold
  (via \texttt{foldM\_spmf}) over the input list with a \texttt{state} record, with
  each loop iteration being modelled by the \texttt{step} function.
  
  \texttt{step} itself is split up into 3 functions, namely:
  \begin{itemize}
    \item \texttt{step\_1} models lines 3 - 4 of algorithm 1
    \item \texttt{step\_2} models lines 5 - 7 of algorithm 1
    \item \texttt{step\_3} models line 8 of algorithm 1
  \end{itemize}
  
  \texttt{cvm} corresponds to algorithm 1, and \texttt{run\_steps} is a
  variation of it that returns the \texttt{state} directly, instead of
  computing and returning the final estimate.\<close>

theory CVM_Algo

imports
  Universal_Hash_Families.Universal_Hash_Families_More_Product_PMF
  Utils_SPMF_Basic

begin

abbreviation f :: real where \<open>f \<equiv> 1 / 2\<close>

record 'a state =
  state_k :: nat
  state_chi :: \<open>'a set\<close>

definition initial_state :: \<open>'a state\<close> where
  \<open>initial_state \<equiv> \<lparr>state_k = 0, state_chi = {}\<rparr>\<close>

definition compute_estimate :: \<open>'a state \<Rightarrow> real\<close> where
  \<open>compute_estimate \<equiv> \<lambda> state. card (state_chi state) / f ^ (state_k state)\<close>

locale cvm_algo =
  fixes threshold :: nat
begin

definition step_1 :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_1 \<equiv> \<lambda> x state. do {
    let k = state_k state; let chi = state_chi state;
    insert_x_into_chi \<leftarrow> bernoulli_pmf <| f ^ k;
    let chi = (chi |>
      if insert_x_into_chi
      then insert x
      else Set.remove x);
    return_pmf (state\<lparr>state_chi := chi\<rparr>) }\<close>

definition step_2 :: \<open>'a state \<Rightarrow> 'a state pmf\<close> where
  \<open>step_2 \<equiv> \<lambda> state.
    let k = state_k state; chi = state_chi state
    in if card chi = threshold
      then do {
        keep_in_chi :: 'a \<Rightarrow> bool \<leftarrow> prod_pmf chi \<lblot>bernoulli_pmf f\<rblot>;
        return_pmf (\<lparr>state_k = Suc k, state_chi = Set.filter keep_in_chi chi\<rparr>) }
      else return_pmf state\<close>

definition step_3 :: \<open>'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step_3 \<equiv> \<lambda> state.
    if card (state_chi state) = threshold
    then fail_spmf
    else return_spmf state\<close>

definition step :: \<open>'a \<Rightarrow> 'a state \<Rightarrow> 'a state spmf\<close> where
  \<open>step \<equiv> \<lambda> x state. spmf_of_pmf (step_1 x state \<bind> step_2) \<bind> step_3\<close>

abbreviation \<open>run_steps \<equiv> foldM_spmf step\<close>

definition cvm :: \<open>'a list \<Rightarrow> real spmf\<close> where
  \<open>cvm xs \<equiv> map_spmf compute_estimate (foldM_spmf step xs initial_state)\<close>

lemmas step_1_def' =
  step_1_def[simplified map_pmf_def[symmetric] Let_def if_distribR]

lemmas step_2_def' =
  step_2_def[simplified map_pmf_def[symmetric] Let_def]

end

locale cvm_algo_assms = cvm_algo + ord_spmf_syntax +
  assumes threshold : \<open>threshold > 0\<close>

end
