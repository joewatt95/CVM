theory Utils_SPMF_FoldM

imports
  "CVM.Utils_SPMF_Common"

begin

fun
  foldM_spmf :: ‹('a ⇒ 'b ⇒ 'b spmf) ⇒ 'a list ⇒ 'b ⇒ 'b spmf› where
  ‹foldM_spmf _ [] acc = return_spmf acc› |
  ‹foldM_spmf f (x # xs) acc = f x acc ⤜ foldM_spmf f xs›

locale spmf_foldM =
  fixes
    f :: ‹'a ⇒ 'b ⇒ 'b spmf› and
    x :: 'a and
    xs :: ‹'a list› and
    acc :: 'b
begin

lemma pmf_foldM_spmf_nil :
  shows
    ‹spmf (foldM_spmf f [] acc) acc = 1› and
    ‹acc ≠ acc' ⟹ spmf (foldM_spmf f [] acc) acc' = 0›
  by auto

lemma pmf_foldM_spmf_cons :
  ‹pmf (foldM_spmf f (x # xs) acc) a
  = ∫ acc'. (
      case acc' of
        None ⇒ pmf fail_spmf a |
        Some acc' ⇒ pmf (foldM_spmf f xs acc') a)
      ∂ f x acc›

  apply (simp add: bind_spmf_def pmf_bind)
  by (metis fail_spmf_def option.case_eq_if)

lemma integrable_prob_fail_foldM_spmf :
  ‹integrable
    (measure_spmf <| f x acc) <|
    prob_fail <<< (foldM_spmf f xs)›

  by (auto
      intro!: measure_spmf.integrable_const_bound[where ?B = 1]
      simp add: prob_fail_def pmf_le_1)

end

end