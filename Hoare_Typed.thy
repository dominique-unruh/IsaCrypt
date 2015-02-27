theory Hoare_Typed
imports Lang_Typed Hoare_Untyped
begin

section {* Definition of Hoare triples *}

definition hoare :: "(memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "hoare pre prog post =
  (\<forall>m. pre m \<longrightarrow> (\<forall>m'. m' \<in> support_distr (denotation prog m) \<longrightarrow> post m'))";

lemma hoare_untyped: "hoare P c Q = hoare_untyped P (mk_program_untyped c) Q"
  unfolding denotation_def hoare_def hoare_untyped_def by simp


section {* Concrete syntax *}

syntax "_hoare" :: "(memory \<Rightarrow> bool) \<Rightarrow> program_syntax \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> term"
          ("hoare {(_)}/ (2_)/ {(_)}")
syntax "_memory" :: memory ("&m")

ML_file "hoare_syntax.ML"

parse_translation {*
    [("_hoare", fn ctx => fn [P,c,Q] => Hoare_Syntax.trans_hoare ctx P c Q)]
*}

print_translation {*
  [(@{const_syntax hoare}, fn ctx => fn [P,c,Q] => Hoare_Syntax.trans_hoare_back ctx P c Q)]
*}

section {* Rules *}

lemma seq_rule:
  fixes P Q R c d
  assumes "hoare {P &m} \<guillemotleft>c\<guillemotright> {Q &m}" and "hoare {Q &m} \<guillemotleft>d\<guillemotright> {R &m}"
  shows "hoare {P &m} \<guillemotleft>c\<guillemotright>;\<guillemotleft>d\<guillemotright> {R &m}"
  using assms seq_rule unfolding hoare_untyped mk_untyped_seq by auto

lemma assign_rule:
  fixes P Q x e
  assumes "\<forall>m. P m \<longrightarrow> Q (memory_update m x (e_fun e m))"
  shows "hoare {P &m} x := \<guillemotleft>e\<guillemotright> {Q &m}"
  unfolding hoare_untyped mk_untyped_assign
  apply (rule assign_rule)
  using assms unfolding memory_update_def by auto

lemma assign_rule':
  fixes P Q c x e
  assumes "hoare {P &m} \<guillemotleft>c\<guillemotright> {Q (memory_update &m x (e_fun e &m))}"
  shows "hoare {P &m} \<guillemotleft>c\<guillemotright>; x := \<guillemotleft>e\<guillemotright> {Q &m}"
by (rule seq_rule, rule assms, rule assign_rule, simp)


lemma while_rule:
  fixes P Q I c e
  assumes "hoare {I &m \<and> e_fun e &m} \<guillemotleft>c\<guillemotright> {I &m}"
          "\<forall>m. P m \<longrightarrow> I m"
          "\<forall>m. \<not> e_fun e m \<longrightarrow> I m \<longrightarrow> Q m"
  shows "hoare {P &m} while (\<guillemotleft>e\<guillemotright>) \<guillemotleft>c\<guillemotright> {Q &m}"
  unfolding hoare_untyped mk_untyped_while
  apply (rule while_rule[where I=I])
  using assms unfolding hoare_untyped e_fun_bool_untyped.

lemma while_rule':
  fixes P Q I c0 c e
  assumes "hoare {I &m \<and> e_fun e &m} \<guillemotleft>c\<guillemotright> {I &m}"
          "hoare {P &m} \<guillemotleft>c0\<guillemotright> {I &m}"
          "\<forall>m. \<not> e_fun e m \<longrightarrow> I m \<longrightarrow> Q m"
  shows "hoare {P &m} \<guillemotleft>c0\<guillemotright>; while (\<guillemotleft>e\<guillemotright>) \<guillemotleft>c\<guillemotright> {Q &m}"
by (rule seq_rule, rule assms, rule while_rule, auto simp: assms)


lemma iftrue_rule:
  assumes "hoare {P &m} \<guillemotleft>c1\<guillemotright> {Q &m}"
          "\<forall>m. P m \<longrightarrow> e_fun e m"
  shows "hoare {P &m} if (\<guillemotleft>e\<guillemotright>) \<guillemotleft>c1\<guillemotright> else \<guillemotleft>c2\<guillemotright> {Q &m}"
  unfolding hoare_untyped mk_untyped_ifte
  apply (rule iftrue_rule)
  using assms unfolding hoare_untyped by auto

lemma iffalse_rule:
  fixes P Q I e p1 p2
  assumes "hoare {P &m} \<guillemotleft>p2\<guillemotright> {Q &m}"
          "\<forall>m. P m \<longrightarrow> \<not> e_fun e m"
  shows "hoare {P &m}   if (\<guillemotleft>e\<guillemotright>) \<guillemotleft>p1\<guillemotright> else \<guillemotleft>p2\<guillemotright>   {Q &m}"
  unfolding hoare_untyped mk_untyped_ifte
  apply (rule iffalse_rule)
  using assms unfolding hoare_untyped by auto

lemma true_rule [simp]: "(\<forall>m. Q m) \<Longrightarrow> hoare {P &m} \<guillemotleft>c\<guillemotright> {Q &m}"
  unfolding hoare_def by simp

lemma skip_rule [simp]:
  assumes "\<forall>m. P m \<longrightarrow> Q m"
  shows "hoare {P &m} skip {Q &m}"
  unfolding hoare_def using assms denotation_skip by simp

lemma skip_rule' [simp]:
  assumes "hoare {P &m} \<guillemotleft>c\<guillemotright> {Q &m}"
  shows "hoare {P &m} \<guillemotleft>c\<guillemotright>; skip {Q &m}"
  by (rule seq_rule, rule assms, rule skip_rule, simp)

lemma conseq_rule:
  assumes "\<forall>m. P m \<longrightarrow> P' m"
      and "\<forall>m. Q' m \<longrightarrow> Q m"
      and "hoare {P' &m} \<guillemotleft>c\<guillemotright> {Q' &m}"
  shows "hoare {P &m} \<guillemotleft>c\<guillemotright> {Q &m}"
  using assms unfolding hoare_def by auto

lemma case_rule:
  assumes "\<And>x. hoare {P &m \<and> f &m = x} \<guillemotleft>c\<guillemotright> {Q &m}"
  shows "hoare {P &m} \<guillemotleft>c\<guillemotright> {Q &m}"
using assms unfolding hoare_def by metis

end