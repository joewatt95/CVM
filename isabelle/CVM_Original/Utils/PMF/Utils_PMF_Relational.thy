theory Utils_PMF_Relational

imports
  Utils_PMF_Hoare

begin

lemmas rel_pmf_mono_strong = rel_spmf_mono_strong[
  where f = \<open>spmf_of_pmf _\<close> and g = \<open>spmf_of_pmf _\<close>,
  simplified]

lemmas rel_pmf_bindI1 = rel_spmf_bindI1[
  where p = \<open>spmf_of_pmf _\<close> and q = \<open>spmf_of_pmf _\<close> and f = \<open>spmf_of_pmf <<< _\<close>,
  simplified,
  simplified spmf_of_pmf_bind[symmetric] rel_spmf_spmf_of_pmf]

lemmas rel_pmf_bindI2 = rel_spmf_bindI2[
  where p = \<open>spmf_of_pmf _\<close> and q = \<open>spmf_of_pmf _\<close> and f = \<open>spmf_of_pmf <<< _\<close>,
  simplified,
  simplified spmf_of_pmf_bind[symmetric] rel_spmf_spmf_of_pmf]

abbreviation relational_hoare_triple
  (\<open>\<turnstile>pmf \<lbrakk> _ \<rbrakk> \<langle> _ | _ \<rangle> \<lbrakk> _ \<rbrakk>\<close> [21, 20, 20, 21] 60) where
  \<open>(\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>S\<rbrakk>) \<equiv> (\<And> x x'. R x x' \<Longrightarrow> rel_pmf S (f x) (f' x'))\<close>

(* lemma precond_strengthen :
  assumes
    \<open>\<And> x x'. R x x' \<Longrightarrow> R' x x'\<close>
    \<open>\<turnstile>pmf \<lbrakk>R'\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>S\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>S\<rbrakk>\<close>
  by (metis assms(1,2) relational_hoare_triple_def)

lemma precond_false [simp] :
  \<open>\<turnstile>pmf \<lbrakk>\<lblot>\<lblot>False\<rblot>\<rblot>\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>S\<rbrakk>\<close>
  by (simp add: relational_hoare_triple_def)

lemma postcond_weaken :
  assumes
    \<open>\<And> x x'. S' x x' \<Longrightarrow> S x x'\<close>
    \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>S'\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>S\<rbrakk>\<close>
  by (metis assms(1,2) pmf.rel_mono_strong relational_hoare_triple_def)

lemma postcond_true [simp] :
  \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>\<lblot>\<lblot>True\<rblot>\<rblot>\<rbrakk>\<close>
  by (smt (verit, best) map_pmf_const pmf.rel_map(1) pmf.rel_mono_strong rel_pmf_return_pmf1 relational_hoare_triple_def) *)

(* lemma refl_eq [simp] :
  \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>\<lblot>x\<rblot> | \<lblot>x\<rblot>\<rangle> \<lbrakk>(=)\<rbrakk>\<close>
  \<open>\<turnstile>pmf \<lbrakk>(=)\<rbrakk> \<langle>f | f\<rangle> \<lbrakk>(=)\<rbrakk>\<close>
  \<open>\<turnstile>pmf \<lbrakk>(\<lambda> x x'. S x x' \<and> x = x')\<rbrakk> \<langle>f | f\<rangle> \<lbrakk>(=)\<rbrakk>\<close>
  \<open>\<turnstile>pmf \<lbrakk>(\<lambda> x x'. x = x' \<and> S x x')\<rbrakk> \<langle>f | f\<rangle> \<lbrakk>(=)\<rbrakk>\<close>
  by (simp_all add: relational_hoare_triple_def pmf.rel_eq) *)

(* lemma skip [simp] :
  \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>return_pmf | return_pmf\<rangle> \<lbrakk>S\<rbrakk> \<equiv>
  (\<And> x x'. R x x' \<Longrightarrow> S x x')\<close>
  by simp *)

(* lemma skip' [simp] :
  \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f >>> return_pmf | f' >>> return_pmf\<rangle> \<lbrakk>S\<rbrakk> \<equiv>
  (\<And> x x'. R x x' \<Longrightarrow> S (f x) (f' x'))\<close>
  by simp *)

lemma skip_left [simp] :
  \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f >>> return_pmf | f'\<rangle> \<lbrakk>S\<rbrakk> \<equiv> (\<And> x. \<turnstile>pmf \<lbrakk>R x\<rbrakk> f' \<lbrakk>S (f x)\<rbrakk>)\<close>
  by (simp add: AE_measure_pmf_iff rel_pmf_return_pmf1)

lemma skip_right [simp] :
  \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f' >>> return_pmf\<rangle> \<lbrakk>S\<rbrakk> \<equiv>
    (\<And> x'. \<turnstile>pmf \<lbrakk>flip R x'\<rbrakk> f \<lbrakk>flip S (f' x')\<rbrakk>)\<close>
  apply standard
  by (simp_all add: AE_measure_pmf_iff rel_pmf_return_pmf2)

(* lemma if_then_else :
  assumes
    \<open>\<And> x x'. R x x' \<Longrightarrow> f x \<longleftrightarrow> f' x'\<close>
    \<open>\<turnstile>pmf \<lbrakk>(\<lambda> x x'. f x \<and> R x x')\<rbrakk> \<langle>g | g'\<rangle> \<lbrakk>S\<rbrakk>\<close>
    \<open>\<turnstile>pmf \<lbrakk>(\<lambda> x x'. \<not> f x \<and> R x x')\<rbrakk> \<langle>h | h'\<rangle> \<lbrakk>S\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf
    \<lbrakk>R\<rbrakk>
    \<langle>(\<lambda> x. if f x then g x else h x) | (\<lambda> x. if f' x then g' x else h' x)\<rangle>
    \<lbrakk>S\<rbrakk>\<close>
  using assms
  by simp *)

(* lemma if_then_else' :
  assumes
    \<open>\<And> x x'. R x x' \<Longrightarrow> f x \<longleftrightarrow> \<not> f' x'\<close>
    \<open>\<turnstile>pmf \<lbrakk>(\<lambda> x x'. f x \<and> R x x')\<rbrakk> \<langle>g | g'\<rangle> \<lbrakk>S\<rbrakk>\<close>
    \<open>\<turnstile>pmf \<lbrakk>(\<lambda> x x'. \<not> f x \<and> R x x')\<rbrakk> \<langle>h | h'\<rangle> \<lbrakk>S\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf
    \<lbrakk>R\<rbrakk>
    \<langle>(\<lambda> x. if f x then g x else h x) | (\<lambda> x. if f' x then h' x else g' x)\<rangle>
    \<lbrakk>S\<rbrakk>\<close>
  using assms by simp  *)

(* lemma seq :
  assumes
    \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>S\<rbrakk>\<close>
    \<open>\<turnstile>pmf \<lbrakk>S\<rbrakk> \<langle>g | g'\<rangle> \<lbrakk>T\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>(\<lambda> x. f x \<bind> g) | (\<lambda> x. f' x \<bind> g')\<rangle> \<lbrakk>T\<rbrakk>\<close>
  using assms
  by (auto
    intro!: rel_pmf_bindI
    simp add: relational_hoare_triple_def) *)

(* lemma seq :
  assumes
    \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f | f'\<rangle> \<lbrakk>S\<rbrakk>\<close>
    \<open>\<And> x x'. R x x' \<Longrightarrow> \<turnstile>pmf \<lbrakk>S\<rbrakk> \<langle>g x | g' x'\<rangle> \<lbrakk>T\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>(\<lambda> x. f x \<bind> g x) | (\<lambda> x. f' x \<bind> g' x)\<rangle> \<lbrakk>T\<rbrakk>\<close>
  using assms rel_pmf_bindI by blast *)

context
  fixes
    R :: \<open>nat \<Rightarrow> 'b \<Rightarrow>'c \<Rightarrow> bool\<close> and
    xs :: \<open>'a list\<close> and
    offset :: nat
begin

private abbreviation (input)
  \<open>foldM_enumerate' fn \<equiv> foldM_pmf_enumerate fn xs offset\<close>

private abbreviation (input)
  \<open>R' index x val val' \<equiv>
    (index, x) \<in> set (List.enumerate offset xs) \<and>
    R index val val'\<close>

lemma loop_enumerate :
  assumes \<open>\<And> index x.
    \<turnstile>pmf \<lbrakk>R' index x\<rbrakk> \<langle>f (index, x) | f' (index, x)\<rangle> \<lbrakk>R (Suc index)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf
    \<lbrakk>R offset\<rbrakk>
    \<langle>foldM_enumerate' f | foldM_enumerate' f'\<rangle>
    \<lbrakk>R (offset + length xs)\<rbrakk>\<close>
using assms proof (induction xs arbitrary: offset)
  case Nil
  then show ?case by (simp add: foldM_enumerate_def)
next
  case (Cons _ _)
  with rel_pmf_bindI show ?case
    apply (simp flip: add_Suc add: foldM_enumerate_def)
    by blast
qed

lemma loop :
  assumes \<open>\<And> index x.
    \<turnstile>pmf \<lbrakk>R' index x\<rbrakk> \<langle>f x | f' x\<rangle> \<lbrakk>R (Suc index)\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf
    \<lbrakk>R offset\<rbrakk>
    \<langle>foldM_pmf f xs | foldM_pmf f' xs\<rangle>
    \<lbrakk>R (offset + length xs)\<rbrakk>\<close>
  using assms loop_enumerate
  by (metis foldM_eq_foldM_enumerate prod.sel(2))

end

lemma loop_unindexed :
  assumes \<open>\<And> x. \<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>f x | f' x\<rangle> \<lbrakk>R\<rbrakk>\<close>
  shows \<open>\<turnstile>pmf \<lbrakk>R\<rbrakk> \<langle>foldM_pmf f xs | foldM_pmf f' xs\<rangle> \<lbrakk>R\<rbrakk>\<close>
  using assms loop[where offset = 0 and R = \<open>\<lblot>R\<rblot>\<close>] by blast

end