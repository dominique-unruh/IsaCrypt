theory Hoare_Typed
imports Lang_Typed Hoare_Untyped
begin



lemma assign_rule:
  fixes P Q c x
  assumes "\<forall>m. P m \<longrightarrow> Q (memory_update m x (e_fun e m))"
  shows "hoare P (assign x e) Q"
  unfolding assign_def 
  apply (rule assign_rule)
  using assms unfolding memory_update_def by auto

lemma while_rule:
  fixes P Q I c e
  assumes "hoare (\<lambda>m. I m \<and> e_fun e m) p I"
          "\<forall>m. P m \<longrightarrow> I m"
          "\<forall>m. \<not> e_fun e m \<longrightarrow> I m \<longrightarrow> Q m"
  shows "hoare P (while e p) Q"
  unfolding while_def 
  apply (rule while_rule[where I=I])
  using assms unfolding e_fun_bool_untyped by auto

end
