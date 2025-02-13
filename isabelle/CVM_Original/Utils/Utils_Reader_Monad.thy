theory Utils_Reader_Monad
  imports "HOL-Library.Monad_Syntax" "Utils_Basic"
begin

datatype ('c, 'a) reader_monad = Reader (run_reader: "'c \<Rightarrow> 'a")

definition bind_rd :: "('c,'a) reader_monad \<Rightarrow> ('a \<Rightarrow> ('c,'b) reader_monad) \<Rightarrow> ('c,'b) reader_monad"
  where "bind_rd m f = Reader (\<lambda>r. run_reader (f (run_reader m r)) r)"

definition return_rd :: "'a \<Rightarrow> ('c,'a) reader_monad"
  where "return_rd m = Reader (\<lambda>_. m)"

definition get_rd :: "('a,'a) reader_monad"
  where "get_rd = Reader id"

definition map_rd :: "('a \<Rightarrow> 'b) \<Rightarrow> ('c, 'a) reader_monad \<Rightarrow> ('c,'b) reader_monad"
  where "map_rd f m = bind_rd m (\<lambda>x. return_rd (f x))"

adhoc_overloading Monad_Syntax.bind == bind_rd

abbreviation (input) kleisli_compose_left
  (infixl \<open>>=>\<close> 50) where
  \<open>(f >=> g) \<equiv> \<lambda> x. bind_rd (f x) g\<close>

abbreviation (input) kleisli_compose_right
  (infixr \<open><=<\<close> 50) where
  \<open>(f <=< g) \<equiv> g >=> f\<close>

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

lemma bind_return_rd :
  \<open>f >=> return_rd = f\<close>
  \<open>return_rd >=> f = f\<close>
  by (simp_all add: bind_rd_def return_rd_def)

lemma bind_assoc_rd :
  \<open>f >=> (g >=> h) = (f >=> g >=> h)\<close>
  by (simp add: bind_rd_def)

lemma reader_monad_eqI:
  assumes "\<And> \<phi>. run_reader m \<phi> = run_reader n \<phi>"
  shows "m = n"
  using assms
  by (metis (mono_tags) reader_monad.rel_eq reader_monad.rel_sel rel_fun_eq_rel)

lemmas bind_cong_rd = arg_cong2[where f = bind_rd]

lemma map_bind_rd:
  "map_rd g (bind_rd m f) = bind_rd m (\<lambda>x. map_rd g (f x))"
  by (intro reader_monad_eqI) simp

lemma map_comp_rd :
  \<open>map_rd g (map_rd f m) = map_rd (g <<< f) m\<close>
  by (simp add: ext reader_monad.expand)

abbreviation hoare_triple
  (\<open>\<turnstile>rd \<lbrakk> _ \<rbrakk> _ \<lbrakk> _ \<rbrakk> \<close> [21, 20, 21] 60) where
  \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> f \<lbrakk>Q\<rbrakk> \<equiv> (\<And> \<phi> x. P \<phi> x \<Longrightarrow> Q \<phi> (run_reader (f x) \<phi>))\<close>

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

lemma loop_enumerate :
  assumes \<open>\<And> idx x. \<turnstile>rd \<lbrakk>P' idx x\<rbrakk> f (idx, x) \<lbrakk>P (Suc idx)\<rbrakk>\<close>
  shows \<open> \<turnstile>rd
    \<lbrakk>P offset\<rbrakk>
    foldM_rd_enumerate f xs offset
    \<lbrakk>P (offset + length xs)\<rbrakk>\<close>
  using assms
  apply (induction xs arbitrary: offset)
  by (simp_all add: foldM_enumerate_def flip: add_Suc)

lemma loop :
  assumes \<open>\<And> idx x. \<turnstile>rd \<lbrakk>P' idx x\<rbrakk> f x \<lbrakk>P (Suc idx)\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>P offset\<rbrakk> foldM_rd f xs \<lbrakk>P (offset + length xs)\<rbrakk>\<close>
  using assms loop_enumerate
  by (metis foldM_eq_foldM_enumerate snd_conv)

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile>rd \<lbrakk>P\<rbrakk> f x \<lbrakk>P\<rbrakk>\<close>
  shows \<open>\<turnstile>rd \<lbrakk>P\<rbrakk> foldM_rd f xs \<lbrakk>P\<rbrakk>\<close>
  using loop[where ?P = \<open>curry <| snd >>> P\<close> and ?offset = 0] assms
  apply simp by blast

end