theory Hoare_Typed
imports Lang_Typed Hoare_Untyped
begin

section {* Concrete syntax *}

syntax "_hoare" :: "(memory \<Rightarrow> bool) \<Rightarrow> program_syntax \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> term"
          ("hoare { _ } _ { _ }")

parse_translation {*
  let
    fun trans_hoare ctx P c Q =
      Const(@{const_syntax Hoare_Untyped.hoare},dummyT) $ P $ translate_program ctx c $ Q
  in
    [("_hoare", fn ctx => fn [P,c,Q] => trans_hoare ctx P c Q)]
  end
*}

section {* Rules *}

lemma assign_rule:
  fixes P Q c x
  assumes "\<forall>m. P m \<longrightarrow> Q (memory_update m x (e_fun e m))"
  shows "hoare {P} x := \<guillemotleft>e\<guillemotright> {Q}"
  unfolding assign_def
  apply (rule assign_rule)
  using assms unfolding memory_update_def by auto

lemma while_rule:
  fixes P Q I c e
  assumes "hoare {\<lambda>m. I m \<and> e_fun e m} \<guillemotleft>p\<guillemotright> {I}"
          "\<forall>m. P m \<longrightarrow> I m"
          "\<forall>m. \<not> e_fun e m \<longrightarrow> I m \<longrightarrow> Q m"
  shows "hoare {P} while \<guillemotleft>(e)\<guillemotright> \<guillemotleft>p\<guillemotright> {Q}"
  unfolding while_def 
  apply (rule while_rule[where I=I])
  using assms unfolding e_fun_bool_untyped.

lemma iftrue_rule:
  fixes P Q I e p1 p2
  assumes "hoare {P} \<guillemotleft>p1\<guillemotright> {Q}"
          "\<forall>m. P m \<longrightarrow> e_fun e m"
  shows "hoare {P} if \<guillemotleft>(e)\<guillemotright> \<guillemotleft>p1\<guillemotright> else \<guillemotleft>p2\<guillemotright> {Q}"
  unfolding ifte_def 
  apply (rule iftrue_rule)
  using assms by auto

lemma iffalse_rule:
  fixes P Q I e p1 p2
  assumes "hoare {P} \<guillemotleft>p2\<guillemotright> {Q}"
          "\<forall>m. P m \<longrightarrow> \<not> e_fun e m"
  shows "hoare {P}   if \<guillemotleft>(e)\<guillemotright> \<guillemotleft>p1\<guillemotright> else \<guillemotleft>p2\<guillemotright>   {Q}"
  unfolding ifte_def 
  apply (rule iffalse_rule)
  using assms by auto

end
