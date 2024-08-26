theory Utils_PMF

imports
  "HOL-Probability.Probability_Mass_Function"

begin

fun foldM_pmf :: "('a \<Rightarrow> 'b \<Rightarrow> 'b pmf) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b pmf" where
  "foldM_pmf _ [] val = return_pmf val" |
  "foldM_pmf f (x # xs) val = f x val \<bind> foldM_pmf f xs"

(*\<bind> 
    bind_pmf (f x val) (foldM_option_pmf f xs)
*)

fun
  foldM_option_pmf :: "
    ('a \<Rightarrow> 'b \<Rightarrow> 'b option pmf) \<Rightarrow>
    'a list \<Rightarrow> 'b \<Rightarrow> 'b option pmf" where "
  foldM_option_pmf _ [] val = return_pmf (Some val)" | "
  foldM_option_pmf f (x # xs) val = do {
    val \<leftarrow> f x val;
    case val of
      Some val \<Rightarrow> foldM_option_pmf f xs val |
      None \<Rightarrow> return_pmf None }"

definition map_option_pmf :: "
  ('a \<Rightarrow> 'b) \<Rightarrow> 'a option pmf \<Rightarrow> 'b option pmf" where
  [simp] : "map_option_pmf \<equiv> map_pmf \<circ> map_option"

(* 
fun unfoldM_option_pmf :: "
  ('b list \<Rightarrow> ('a \<times> 'b list) option pmf) \<Rightarrow> 'b list \<Rightarrow> 'a option list pmf" where "
  unfoldM_option_pmf f (b # bs) = do {
    b \<leftarrow> f b;
    case b of
      Some (a, bs) \<Rightarrow> do {
        _ \<leftarrow> unfoldM_option_pmf f bs;
        undefined
      } |
      None \<Rightarrow> undefined
    }" *)
(* 
fun
  traverse_option_pmf :: "
    ('a \<Rightarrow> 'b option pmf) \<Rightarrow> 'a option pmf list \<Rightarrow> 'b option list pmf" where "
  traverse_option_pmf _ [] = return_pmf []" | "
  traverse_option_pmf f (x # xs) = do {
    ys \<leftarrow> traverse_option_pmf f xs;
    x \<leftarrow> x;
    case x of
      Some x \<Rightarrow> do {
        y \<leftarrow> f x;
        return_pmf (y # ys) } |
      None \<Rightarrow> return_pmf (None # ys) }" *)

end