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
  sorry

lemma assign_rule:
  fixes P Q c x
  assumes "\<forall>m. P m \<longrightarrow> Q (memory_update_untyped m x (eu_fun e m))"
  shows "hoare P (Assign x e) Q"
  sorry

lemma while_rule:
  fixes P Q I c e
  assumes "hoare (\<lambda>m. I m \<and> eu_fun e m = embedding True) p I"
          "\<forall>m. P m \<longrightarrow> I m"
          "\<forall>m. eu_fun e m \<noteq> embedding True \<longrightarrow> I m \<longrightarrow> Q m"
  shows "hoare P (While e p) Q"
  sorry

end
