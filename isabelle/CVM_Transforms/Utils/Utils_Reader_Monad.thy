section \<open>Reader monad\<close>

text \<open>Reader monad ala Haskell.\<close>

theory Utils_Reader_Monad

imports
  "Utils_Basic"

begin

datatype ('c, 'a) reader_monad = Reader (run_reader: "'c \<Rightarrow> 'a")

definition bind_rd :: "('c,'a) reader_monad \<Rightarrow> ('a \<Rightarrow> ('c,'b) reader_monad) \<Rightarrow> ('c,'b) reader_monad"
  where "bind_rd m f \<equiv> Reader (\<lambda>r. run_reader (f (run_reader m r)) r)"

definition return_rd :: "'a \<Rightarrow> ('c,'a) reader_monad"
  where "return_rd m \<equiv> Reader (\<lambda> _. m)"

definition get_rd :: "('a,'a) reader_monad"
  where "get_rd \<equiv> Reader id"

definition map_rd :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c, 'a) reader_monad \<Rightarrow> ('c,'b) reader_monad"
  where "map_rd f m \<equiv> bind_rd m (\<lambda>x. return_rd (f x))"

(* Isabelle2025:
adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> bind_rd *)
adhoc_overloading Monad_Syntax.bind bind_rd

abbreviation \<open>foldM_rd \<equiv> foldM bind_rd return_rd\<close>
abbreviation \<open>foldM_rd_enumerate \<equiv> foldM_enumerate bind_rd return_rd\<close>

lemma foldM_rd_snoc: "foldM_rd f (xs@[y]) val = bind_rd (foldM_rd f xs val) (f y)"
  by (induction xs arbitrary:val) (auto simp:bind_rd_def return_rd_def)

lemma run_reader_simps [simp] :
  "run_reader (return_rd x) \<phi> = x"
  "run_reader get_rd \<phi> = \<phi>"
  "run_reader (m \<bind> f) \<phi> = run_reader (f (run_reader m \<phi>)) \<phi>"
  "run_reader (map_rd g m) \<phi> = (g (run_reader m \<phi>))"
  unfolding map_rd_def return_rd_def get_rd_def bind_rd_def by auto

lemma bind_return_rd [simp] :
  \<open>f >=> return_rd = f\<close>
  \<open>return_rd >=> f = f\<close>

  \<open>f x \<bind> return_rd = f x\<close>
  \<open>return_rd x \<bind> f = f x\<close>
  by (simp_all add: bind_rd_def return_rd_def)

lemma bind_assoc_rd [simp] :
  \<open>f >=> (\<lambda> x. bind_rd (g x) h) = (f >=> g >=> h)\<close>
  \<open>f x \<bind> (\<lambda>x. g x \<bind> h) = (f x \<bind> g \<bind> h)\<close>
  by (simp_all add: bind_rd_def)

lemma reader_monad_eqI:
  assumes "\<And> \<phi>. run_reader m \<phi> = run_reader n \<phi>"
  shows "m = n"
  using assms
  by (metis (mono_tags) reader_monad.rel_eq reader_monad.rel_sel rel_fun_eq_rel)

lemmas bind_cong_rd = arg_cong2[where f = bind_rd]

lemma map_bind_rd:
  "map_rd g (bind_rd m f) = bind_rd m (\<lambda> x. map_rd g (f x))"
  by (intro reader_monad_eqI) simp

lemma map_comp_rd :
  \<open>map_rd g (map_rd f m) = map_rd (g <<< f) m\<close>
  by (simp add: ext reader_monad.expand)

subsection \<open>foldM\_rd and related Hoare rules\<close>

subsubsection \<open>Hoare triple for Kleisli morphisms over Reader monad\<close>

abbreviation hoare_triple
  (\<open>\<turnstile>rd \<lbrakk> _ \<rbrakk> _ \<lbrakk> _ \<rbrakk> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<equiv> (\<And> \<phi> x. P \<phi> x \<Longrightarrow> Q \<phi> <| run_reader (f x) \<phi>)\<close>

subsubsection \<open>Hoare rules for foldM\_rd\<close>

context
  fixes
    P :: \<open>nat \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

private abbreviation (input)
  \<open>P' \<equiv> \<lambda> idx x \<phi> val.
    (idx, x) \<in> set (List.enumerate offset xs) \<and>
    P idx \<phi> val\<close>

lemma hoare_foldM_enumerate :
  assumes \<open>\<And> idx x. \<turnstile>rd \<lbrakk>P' idx x\<rbrakk> f (idx, x) \<lbrakk>P (Suc idx)\<rbrakk>\<close>
  shows \<open> \<turnstile>rd
    \<lbrakk>P offset\<rbrakk>
    foldM_rd_enumerate f xs offset
    \<lbrakk>P (offset + length xs)\<rbrakk>\<close>
  using assms apply (induction xs arbitrary: offset)
    by (simp_all add: foldM_enumerate_def flip: add_Suc)

lemma hoare_foldM_indexed' :
  assumes \<open>\<And> idx x. \<turnstile>rd \<lbrakk>P' idx x\<rbrakk> f x \<lbrakk>P (Suc idx)\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>P offset\<rbrakk> foldM_rd f xs \<lbrakk>P (offset + length xs)\<rbrakk>\<close>
  using assms hoare_foldM_enumerate
  by (metis foldM_eq_foldM_enumerate snd_conv)

end

lemmas hoare_foldM_indexed = hoare_foldM_indexed'[where offset = 0, simplified]

lemma hoare_foldM :
  assumes \<open>\<And> x. \<turnstile>rd \<lbrakk>P\<rbrakk> f x \<lbrakk>P\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> foldM_rd f xs \<lbrakk>P\<rbrakk>\<close>
  using assms hoare_foldM_indexed[where P = \<open>\<lblot>P\<rblot>\<close>] by blast

end