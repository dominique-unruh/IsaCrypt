theory Hoare_Untyped
imports Lang_Untyped
begin

definition hoare_untyped :: "(memory \<Rightarrow> bool) \<Rightarrow> program_rep \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "hoare_untyped pre prog post =
  (\<forall>m. pre m \<longrightarrow> (\<forall>m'. m' \<in> support_distr (denotation_untyped prog m) 
                  \<longrightarrow> post m'))"

lemma seq_rule:
  fixes P Q R c d
  assumes "hoare_untyped P c Q" and "hoare_untyped Q d R"
  shows "hoare_untyped P (Seq c d) R"
  using assms unfolding hoare_untyped_def by auto

lemma assign_rule:
  fixes P Q c x
  assumes "\<forall>m. P m \<longrightarrow> Q (memory_update_untyped m x (eu_fun e m))"
  shows "hoare_untyped P (Assign x e) Q"
  using assms unfolding hoare_untyped_def by simp

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


end
