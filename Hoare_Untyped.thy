theory Hoare_Untyped
imports Lang_Untyped
begin

definition hoare_untyped :: "(memory \<Rightarrow> bool) \<Rightarrow> program_rep \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "hoare_untyped pre prog post =
  (\<forall>m. pre m \<longrightarrow> (\<forall>m'. m' \<in> support_distr (denotation_untyped prog m) 
                  \<longrightarrow> post m'))"

definition hoare_denotation :: "(memory \<Rightarrow> bool) \<Rightarrow> _ \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "hoare_denotation pre prog post = (\<forall>m. pre m \<longrightarrow> (\<forall>m'. m' \<in> support_distr (prog m) \<longrightarrow> post m'))"

lemma hoare_untyped_hoare_denotation: "hoare_untyped pre c post = hoare_denotation pre (denotation_untyped c) post"
  unfolding hoare_untyped_def hoare_denotation_def ..



lemma seq_rule:
  fixes P Q R c d
  assumes "hoare_untyped P c Q" and "hoare_untyped Q d R"
  shows "hoare_untyped P (Seq c d) R"
  using assms unfolding hoare_untyped_def by auto

lemma assign_rule:
  fixes P Q xs gs e
  assumes "\<forall>m. P m \<longrightarrow> Q (memory_update_untyped_pattern m pat (eu_fun e m))"
  shows "hoare_untyped P (Assign pat e) Q"
  using assms unfolding hoare_untyped_def by simp

lemma sample_rule: 
  fixes P Q xs gs e
  assumes "\<forall>m. P m \<longrightarrow> (\<forall>v\<in>support_distr (ed_fun e m). Q (memory_update_untyped_pattern m pat v))"
  shows "hoare_untyped P (Sample pat e) Q"
  using assms unfolding hoare_untyped_def by auto

lemma while_rule:
  fixes P Q I c p
  assumes "hoare_untyped (\<lambda>m. I m \<and> eu_fun e m = embedding True) p I"
          "\<forall>m. P m \<longrightarrow> I m"
          "\<forall>m. eu_fun e m \<noteq> embedding True \<longrightarrow> I m \<longrightarrow> Q m"
  shows "hoare_untyped P (While e p) Q"
  SORRY

lemma iftrue_rule:
  fixes P Q I c p1 p2
  assumes "hoare_untyped P p1 Q"
          "\<forall>m. P m \<longrightarrow> eu_fun e m = embedding True"
  shows "hoare_untyped P (IfTE e p1 p2) Q"
  using assms unfolding hoare_untyped_def by auto

lemma iffalse_rule:
  fixes P Q I c p1 p2
  assumes "hoare_untyped P p2 Q"
          "\<forall>m. P m \<longrightarrow> eu_fun e m \<noteq> embedding True"
  shows "hoare_untyped P (IfTE e p1 p2) Q"
  using assms unfolding hoare_untyped_def by simp

lemma true_rule: "(\<forall>m. Q m) \<Longrightarrow> hoare_untyped P c Q"
  unfolding hoare_untyped_def by simp

lemma skip_rule:
  assumes "\<forall>m. P m \<longrightarrow> Q m"
  shows "hoare_untyped P Skip Q"
  unfolding hoare_untyped_def using assms by simp

lemma conseq_rule:
  assumes "\<forall>m. P m \<longrightarrow> P' m"
      and "\<forall>m. Q' m \<longrightarrow> Q m"
      and "hoare_untyped P' c Q'"
  shows "hoare_untyped P c Q"
  using assms unfolding hoare_untyped_def by auto

lemma case_rule:
  assumes "\<And>x. hoare_untyped (\<lambda>m. P m \<and> f m = x) c Q"
  shows "hoare_untyped P c Q"
using assms unfolding hoare_untyped_def by metis

(* TODO move *)
lemma readonly_notin_vars: 
  fixes x::variable_untyped and a::val and c::program_rep
  assumes "x\<notin>set(vars_untyped c)"
  shows "hoare_untyped (\<lambda>m. memory_lookup_untyped m x = a) c (\<lambda>m. memory_lookup_untyped m x = a)"
SORRY

(* TODO move *)
lemma readonly_assign: 
  fixes x::pattern_untyped and y::variable_untyped and e::expression_untyped and a::val
  assumes "y\<notin>set(p_vars x)"
  shows "hoare_untyped (\<lambda>m. memory_lookup_untyped m y = a) (Assign x e) (\<lambda>m. memory_lookup_untyped m y = a)"
SORRY


end
