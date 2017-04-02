theory Hoare_Typed
imports Lang_Typed Hoare_Untyped
begin

subsection {* Definition of Hoare triples *}

definition hoare :: "(memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "hoare pre prog post =
  (\<forall>m. pre m \<longrightarrow> (\<forall>m'. m' \<in> support_distr (denotation prog m) \<longrightarrow> post m'))"

lemma hoare_untyped: "hoare P c Q = hoare_untyped P (Rep_program c) Q"
  unfolding denotation_def hoare_def hoare_untyped_def by simp

(*
subsection {* Concrete syntax *}

syntax "_hoare" :: "(memory \<Rightarrow> bool) \<Rightarrow> program_syntax \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> term"
          ("hoare {(_)}/ (2_)/ {(_)}")
syntax "_memory" :: memory ("&m")
syntax "_assertion" :: "(memory \<Rightarrow> bool) \<Rightarrow> (memory \<Rightarrow> bool)" ("ASSERTION[_]")

ML_file "hoare_syntax.ML"

parse_translation {*
    [("_hoare", fn ctx => fn [P,c,Q] => Hoare_Syntax.trans_hoare ctx P c Q),
     ("_assertion", fn ctx => fn [P] => Hoare_Syntax.trans_assertion ctx P)]
*}

(* print_translation {*
  [(@{const_syntax hoare}, fn ctx => fn [P,c,Q] => Hoare_Syntax.trans_hoare_back ctx P c Q)]
*} *)
*)
    
subsection {* Rules *}

lemma assertion_footprint_lookup: "mk_variable_untyped x \<in> X \<Longrightarrow> assertion_footprint X (\<lambda>m. memory_lookup m x)"
  unfolding assertion_footprint_def by auto

lemma seq_rule:
  fixes P Q R c d
  assumes "hoare P c Q" and "hoare Q d R"
  shows "hoare P (seq c d) R"
  using assms seq_rule unfolding hoare_untyped by auto

lemma assign_rule:
  fixes P Q x e
  assumes "\<forall>m. P m \<longrightarrow> Q (memory_update_pattern m x (e_fun e m))"
  shows "hoare P (assign x e) Q"
  unfolding hoare_untyped Rep_assign
  apply (rule assign_rule)
  using assms unfolding memory_update_pattern_def by auto

lemma assign_rule':
  fixes P Q c x e
  assumes "hoare P c (\<lambda>m. Q (memory_update_pattern m x (e_fun e m)))"
  shows "hoare P (seq c (assign x e)) Q"
by (rule seq_rule, rule assms, rule assign_rule, simp)

lemma sample_rule:
  fixes P Q x e
  assumes "\<forall>m. P m \<longrightarrow> (\<forall>v\<in>support_distr (e_fun e m). Q (memory_update_pattern m x v))"
  shows "hoare P (sample x e) Q"
  unfolding hoare_untyped Rep_sample 
  apply (rule sample_rule)
  using assms unfolding memory_update_pattern_def by auto

lemma sample_rule':
  fixes P Q c x e
  assumes "hoare P c (\<lambda>m. \<forall>v\<in>support_distr (e_fun e m). Q (memory_update_pattern m x v))"
  shows "hoare P (seq c (sample x e)) Q"
by (rule seq_rule, rule assms, rule sample_rule, simp)

lemma while_rule:
  fixes P Q I c e
  assumes "hoare (\<lambda>m. I m \<and> e_fun e m) c I"
          "\<forall>m. P m \<longrightarrow> I m"
          "\<forall>m. \<not> e_fun e m \<longrightarrow> I m \<longrightarrow> Q m"
  shows "hoare P (while e c) Q"
  unfolding hoare_untyped Rep_while
  apply (rule while_rule[where I=I])
  using assms unfolding hoare_untyped e_fun_bool_untyped.

lemma while_rule':
  fixes P Q I c0 c e
  assumes "hoare (\<lambda>m. I m \<and> e_fun e m) c I"
          "hoare P c0 I"
          "\<forall>m. \<not> e_fun e m \<longrightarrow> I m \<longrightarrow> Q m"
  shows "hoare P (seq c0 (while e c)) Q"
by (rule seq_rule, rule assms, rule while_rule, auto simp: assms)

lemma iftrue_rule:
  assumes "hoare P c1 Q"
          "\<forall>m. P m \<longrightarrow> e_fun e m"
  shows "hoare P (ifte e c1 c2) Q"
  unfolding hoare_untyped Rep_ifte
  apply (rule iftrue_rule)
  using assms unfolding hoare_untyped by auto

lemma iffalse_rule:
  fixes P Q I e p1 p2
  assumes "hoare P p2 Q"
          "\<forall>m. P m \<longrightarrow> \<not> e_fun e m"
  shows "hoare P (ifte e p1 p2) Q"
  unfolding hoare_untyped Rep_ifte
  apply (rule iffalse_rule)
  using assms unfolding hoare_untyped by auto

lemma true_rule [simp]: "(\<forall>m. Q m) \<Longrightarrow> hoare P c Q"
  unfolding hoare_def by simp

lemma skip_rule [simp]:
  assumes "\<forall>m. P m \<longrightarrow> Q m"
  shows "hoare P skip Q"
  unfolding hoare_def using assms denotation_skip by simp

lemma skip_rule' [simp]:
  assumes "hoare P c Q"
  shows "hoare P (seq c skip) Q"
  by (rule seq_rule, rule assms, rule skip_rule, simp)

lemma conseq_rule:
  assumes "\<forall>m. P m \<longrightarrow> P' m"
      and "\<forall>m. Q' m \<longrightarrow> Q m"
      and "hoare P' c Q'"
  shows "hoare P c Q"
  using assms unfolding hoare_def by auto

lemma case_rule:
  assumes "\<And>x. hoare (\<lambda>m. P m \<and> f m = x) c Q"
  shows "hoare P c Q"
using assms unfolding hoare_def by metis

lemma addskip_rule:
  assumes "hoare P (seq skip c) Q"
  shows "hoare P c Q"
  using assms unfolding hoare_def denotation_seq_skip by simp

lemma denotation_eq_rule:
  assumes "denotation d = denotation c"
  assumes "hoare P c Q"
  shows   "hoare P d Q"
using assms unfolding hoare_def by auto

section {* Rules for ML tactics *}

lemma seq_assoc_rule: 
  assumes "hoare P (seq (seq a b) c) R"
  shows "hoare P (seq a (seq b c)) R"
using assms denotation_seq_assoc hoare_def by auto


(* Ordering of subgoals for certain tactics *)
lemma seq_rule_lastfirst:
  fixes P Q R c d
  assumes "hoare Q d R" and "hoare P c Q"
  shows "hoare P (seq c d) R"
  using assms seq_rule unfolding hoare_untyped Rep_seq by auto

lemma assign_rule_strict:
  fixes Q x e
  defines "Q' == \<lambda>m. Q (memory_update_pattern m x (e_fun e m))"
  shows "hoare {Q' &m} \<guillemotleft>assign x e\<guillemotright> {Q &m}"
  apply (rule assign_rule)
  unfolding Q'_def by simp

lemma sample_rule_strict:
  fixes Q x e
  defines "Q' == \<lambda>m. \<forall>v\<in>support_distr (e_fun e m). Q (memory_update_pattern m x v)"
  shows "hoare {Q' &m} \<guillemotleft>sample x e\<guillemotright> {Q &m}"
  apply (rule sample_rule)
  unfolding Q'_def by simp

lemma skip_rule_strict: "hoare {P &m} skip {P &m}"
  by (rule skip_rule, simp)

lemma if_case_rule:
  assumes "hoare {P1 &m} \<guillemotleft>c1\<guillemotright> {Q &m}"
  assumes "hoare {P2 &m} \<guillemotleft>c2\<guillemotright> {Q &m}"
  shows "hoare (* {(e_fun e &m \<longrightarrow> P1 &m) \<and> (\<not> e_fun e &m \<longrightarrow> P2 &m)} *)
               {if e_fun e &m then P1 &m else P2 &m}
                 if (\<guillemotleft>e\<guillemotright>) \<guillemotleft>c1\<guillemotright> else \<guillemotleft>c2\<guillemotright> 
               {Q &m}"
  apply (rule case_rule[where f="\<lambda>m. e_fun e m"])
  apply (case_tac x, auto)
  apply (rule iftrue_rule)
  apply (rule conseq_rule[where P'=P1 and Q'=Q], auto simp: assms)
  apply (rule iffalse_rule)
  by (rule conseq_rule[where P'=P2 and Q'=Q], auto simp: assms)

lemma readonly_hoare:
  shows "program_readonly X c = (\<forall>a. hoare {\<forall>x\<in>X. memory_lookup_untyped &m x = a x} \<guillemotleft>c\<guillemotright> {\<forall>x\<in>X. memory_lookup_untyped &m x = a x})"
using denotation_def hoare_untyped program_readonly_def program_untyped_readonly_def readonly_hoare_untyped by auto

lemma seq_swap:
  fixes A B R
  assumes a_ro: "program_readonly R a"
  assumes b_ro: "program_readonly R b"
  assumes foot_a: "program_footprint A a"
  assumes foot_b: "program_footprint B b"
  assumes ABR: "A\<inter>B\<subseteq>R"
  shows "denotation (seq a b) = denotation (seq b a)"
unfolding denotation_def apply simp apply (rule seq_swap_untyped[THEN ext])
using assms
unfolding program_readonly_def program_untyped_readonly_def denotation_def program_footprint_def program_untyped_footprint_def
by auto


lemma program_readonly_write_vars: "program_readonly (- set(write_vars p)) p"
  using program_untyped_readonly_write_vars[of "Rep_program p"]
  unfolding program_readonly_def program_untyped_readonly_def write_vars_def denotation_def 
  by assumption


end
