theory Hoare_Untyped
imports Lang_Untyped
begin

definition hoare :: "(memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "hoare pre prog post =
  (\<forall>m. pre m \<longrightarrow> (\<forall>m'. m' \<in> support_ell1 (denotation prog m) 
                  \<longrightarrow> post m'))";

lemma seq_rule:
  fixes P Q R c d
  assumes "hoare P c Q" and "hoare Q d R"
  shows "hoare P (Seq c d) R"
  using assms unfolding hoare_def by auto

lemma assign_rule:
  fixes P Q c x
  assumes "\<forall>m. P m \<longrightarrow> Q (memory_update_untyped m x (eu_fun e m))"
  shows "hoare P (Assign x e) Q"
  using assms unfolding hoare_def by simp

lemma while_rule:
  fixes P Q I c p
  assumes "hoare (\<lambda>m. I m \<and> eu_fun e m = embedding True) p I"
          "\<forall>m. P m \<longrightarrow> I m"
          "\<forall>m. eu_fun e m \<noteq> embedding True \<longrightarrow> I m \<longrightarrow> Q m"
  shows "hoare P (While e p) Q"
  sorry

lemma iftrue_rule:
  fixes P Q I c p1 p2
  assumes "hoare P p1 Q"
          "\<forall>m. P m \<longrightarrow> eu_fun e m = embedding True"
  shows "hoare P (IfTE e p1 p2) Q"
  using assms unfolding hoare_def by auto

lemma iffalse_rule:
  fixes P Q I c p1 p2
  assumes "hoare P p2 Q"
          "\<forall>m. P m \<longrightarrow> eu_fun e m \<noteq> embedding True"
  shows "hoare P (IfTE e p1 p2) Q"
  using assms unfolding hoare_def by simp

lemma true_rule: "(\<forall>m. Q m) \<Longrightarrow> hoare P c Q"
  unfolding hoare_def by simp

lemma skip_rule:
  assumes "\<forall>m. P m \<longrightarrow> Q m"
  shows "hoare P Skip Q"
  unfolding hoare_def using assms by simp

lemma conseq_rule:
  assumes "\<forall>m. P m \<longrightarrow> P' m"
      and "\<forall>m. Q' m \<longrightarrow> Q m"
      and "hoare P' c Q'"
  shows "hoare P c Q"
  using assms unfolding hoare_def by auto

end
