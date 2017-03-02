theory RHL_Typed
imports RHL_Untyped Hoare_Typed Procs_Typed
begin

subsection {* Definition *}

definition rhoare :: "(memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> program \<Rightarrow> (memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "rhoare pre c1 c2 post =
  (\<forall>m1 m2. pre m1 m2 \<longrightarrow> 
     (\<exists>\<mu>. apply_to_distr fst \<mu> = denotation c1 m1
        \<and> apply_to_distr snd \<mu> = denotation c2 m2
        \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> post m1' m2')))"


lemma rhoareI: 
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow>
            (\<exists>\<mu>. apply_to_distr fst \<mu> = denotation p1 m1 \<and>
                  apply_to_distr snd \<mu> = denotation p2 m2 \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2'))"
  shows "rhoare P p1 p2 Q"
unfolding rhoare_def using assms by simp

lemma rhoare_untyped: "rhoare P c1 c2 Q = rhoare_untyped P (Rep_program c1) (Rep_program c2) Q"
  unfolding rhoare_def rhoare_untyped_def denotation_def by rule


definition "obs_eq X Y c1 c2 ==
  rhoare (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)
         c1 c2
         (\<lambda>m1 m2. \<forall>x\<in>Y. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
definition "obs_eq' X == obs_eq X X"

lemma obs_eq_obs_eq_untyped: "obs_eq X Y c1 c2 = obs_eq_untyped X Y (Rep_program c1) (Rep_program c2)"
  unfolding obs_eq_def obs_eq_untyped_def rhoare_def
  unfolding rhoare_untyped_def denotation_def by auto

subsection {* Concrete syntax *}

syntax "_rhoare" :: "(memory \<Rightarrow> bool) \<Rightarrow> program_syntax \<Rightarrow> program_syntax \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> term"
          ("hoare {(_)}/ (2_) ~ (2_)/ {(_)}")
syntax "_memory" :: memory ("&m")
syntax "_memory1" :: memory ("&1")
syntax "_memory2" :: memory ("&2")
syntax "_select_memory1" :: "'a \<Rightarrow> 'a" ("_\<^sub>1" [1000] 1000)
syntax "_select_memory2" :: "'a \<Rightarrow> 'a" ("_\<^sub>2" [1000] 1000)

ML_file "rhoare_syntax.ML"

parse_translation {*
  let
  in
    [("_rhoare", fn ctx => fn [P,c1,c2,Q] => RHoare_Syntax.trans_hoare ctx P c1 c2 Q)]
  end
*}



print_translation {*
  [(@{const_syntax RHL_Typed.rhoare}, fn ctx => fn [P,c1,c2,Q] => RHoare_Syntax.trans_hoare_back ctx P c1 c2 Q)]
*}

(* ML {* val testterm = @{term "hoare {True} skip ~ skip {True}"} *}
ML {* Syntax.string_of_term @{context} testterm |> writeln *} *)


(*
term "x\<^sub>a"
ML {* @{print} @{term x\<^sub>a} *}

consts x::"int variable"
consts f::"memory\<Rightarrow>memory"
term "hoare {(x)\<^sub>1 = undefined} skip ~ skip {undefined}"
*)

subsection {* Rules *}

lemma rconseq_rule:
  assumes "\<forall>m m'. P m m' \<longrightarrow> P' m m'"
      and "\<forall>m m'. Q' m m' \<longrightarrow> Q m m'"
      and "hoare {P' &1 &2} \<guillemotleft>c\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {Q' &1 &2}"
  shows "hoare {P &1 &2} \<guillemotleft>c\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {Q &1 &2}"
  using assms unfolding rhoare_def by blast

lemma rseq_rule:
  assumes PcQ: "rhoare P c1 c2 Q"
  assumes QcR: "rhoare Q c1' c2' R"
  shows "rhoare P (seq c1 c1') (seq c2 c2') R"
using assms unfolding rhoare_untyped Rep_seq by (rule rseq_rule)

lemma rsymmetric_rule:
  assumes "hoare {P &1 &2} \<guillemotleft>c\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {Q &1 &2}"
  shows "hoare {P &2 &1} \<guillemotleft>d\<guillemotright> ~ \<guillemotleft>c\<guillemotright> {Q &2 &1}"
using assms rhoare_untyped rsymmetric_rule by auto

lemma assign_left_rule:
  fixes P Q x e
  assumes "\<forall>m m'. P m m' \<longrightarrow> Q (memory_update_pattern m x (e_fun e m)) m'"
  shows "hoare {P &1 &2} \<guillemotleft>assign x e\<guillemotright> ~ skip {Q &1 &2}"
  unfolding rhoare_untyped Rep_skip Rep_assign
  apply (rule rassign_rule1)
  using assms unfolding memory_update_pattern_def by auto

lemma assign_right_rule:
  fixes P Q x e
  assumes "\<forall>m m'. P m m' \<longrightarrow> Q m (memory_update_pattern m' x (e_fun e m'))"
  shows "hoare {P &1 &2} skip ~ \<guillemotleft>assign x e\<guillemotright> {Q &1 &2}"
  unfolding rhoare_untyped Rep_skip Rep_assign
  apply (rule rassign_rule2)
  using assms unfolding memory_update_pattern_def by auto

lemma assign_rule_left_strict:
  fixes Q x e
  defines "Q' == \<lambda>m m'. Q (memory_update_pattern m x (e_fun e m)) m'"
  shows "hoare {Q' &1 &2} \<guillemotleft>assign x e\<guillemotright> ~ skip {Q &1 &2}"
  apply (rule assign_left_rule)
  unfolding Q'_def by simp

lemma assign_rule_right_strict:
  fixes Q x e
  defines "Q' == \<lambda>m m'. Q m (memory_update_pattern m' x (e_fun e m'))"
  shows "hoare {Q' &1 &2} skip ~ \<guillemotleft>assign x e\<guillemotright> {Q &1 &2}"
  apply (rule assign_right_rule)
  unfolding Q'_def by simp

(*lemma sample_rule_left_strict:
  fixes Q x e
  defines "Q' == \<lambda>m m'. \<forall>v\<in>support_distr (e_fun e m). Q (memory_update_pattern m x v) m'"
  shows "hoare {Q' &1 &2} \<guillemotleft>sample x e\<guillemotright> ~ skip {Q &1 &2}"
  apply (rule sample_rule)
  unfolding Q'_def by simp*)




lemma rcase_rule:
  assumes "\<And>x. hoare {P &1 &2 \<and> f &1 &2 = x} \<guillemotleft>c\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {Q &1 &2}"
  shows "hoare {P &1 &2} \<guillemotleft>c\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {Q &1 &2}"
using assms unfolding rhoare_def by metis

lemma iftrue_rule_left:
  assumes "hoare {P &1 &2} \<guillemotleft>c1\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {Q &1 &2}"
          "\<forall>m m'. P m m' \<longrightarrow> e_fun e m"
  shows "hoare {P &1 &2} if (\<guillemotleft>e\<guillemotright>) \<guillemotleft>c1\<guillemotright> else \<guillemotleft>c2\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {Q &1 &2}"
  unfolding rhoare_untyped Rep_ifte
  apply (rule iftrue_rule_left)
  using assms unfolding rhoare_untyped by auto

lemma iffalse_rule_left:
  fixes P Q I e p1 p2
  assumes "hoare {P &1 &2} \<guillemotleft>p2\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {Q &1 &2}"
          "\<forall>m m'. P m m' \<longrightarrow> \<not> e_fun e m"
  shows "hoare {P &1 &2}   if (\<guillemotleft>e\<guillemotright>) \<guillemotleft>p1\<guillemotright> else \<guillemotleft>p2\<guillemotright> ~ \<guillemotleft>d\<guillemotright>   {Q &1 &2}"
  unfolding rhoare_untyped Rep_ifte
  apply (rule iffalse_rule_left)
  using assms unfolding rhoare_untyped by auto

lemma iftrue_rule_right:
  assumes "hoare {P &1 &2} \<guillemotleft>d\<guillemotright> ~ \<guillemotleft>c1\<guillemotright> {Q &1 &2}"
          "\<forall>m m'. P m m' \<longrightarrow> e_fun e m'"
  shows "hoare {P &1 &2} \<guillemotleft>d\<guillemotright> ~ if (\<guillemotleft>e\<guillemotright>) \<guillemotleft>c1\<guillemotright> else \<guillemotleft>c2\<guillemotright> {Q &1 &2}"
  unfolding rhoare_untyped Rep_ifte
  apply (rule iftrue_rule_right)
  using assms unfolding rhoare_untyped by auto

lemma iffalse_rule_right:
  fixes P Q I e p1 p2
  assumes "hoare {P &1 &2} \<guillemotleft>d\<guillemotright> ~ \<guillemotleft>p2\<guillemotright> {Q &1 &2}"
          "\<forall>m m'. P m m' \<longrightarrow> \<not> e_fun e m'"
  shows "hoare {P &1 &2}   \<guillemotleft>d\<guillemotright> ~ if (\<guillemotleft>e\<guillemotright>) \<guillemotleft>p1\<guillemotright> else \<guillemotleft>p2\<guillemotright>   {Q &1 &2}"
  unfolding rhoare_untyped Rep_ifte
  apply (rule iffalse_rule_right)
  using assms unfolding rhoare_untyped by auto


lemma if_case_rule_left:
  assumes "hoare {P1 &1 &2} \<guillemotleft>c1\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {Q &1 &2}"
  assumes "hoare {P2 &1 &2} \<guillemotleft>c2\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {Q &1 &2}"
  shows "hoare {if e_fun e &1 then P1 &1 &2 else P2 &1 &2}
                 if (\<guillemotleft>e\<guillemotright>) \<guillemotleft>c1\<guillemotright> else \<guillemotleft>c2\<guillemotright> ~ \<guillemotleft>d\<guillemotright>
               {Q &1 &2}"
apply (rule rcase_rule[where f="\<lambda>m1 m2. e_fun e m1"])
apply (case_tac x, auto)
 apply (rule iftrue_rule_left)
  apply (rule rconseq_rule[where P'=P1 and Q'=Q], auto simp: assms)[2]
apply (rule iffalse_rule_left)
 by (rule rconseq_rule[where P'=P2 and Q'=Q], auto simp: assms)

lemma if_case_rule_right:
  assumes "hoare {P1 &1 &2} \<guillemotleft>c\<guillemotright> ~ \<guillemotleft>d1\<guillemotright> {Q &1 &2}"
  assumes "hoare {P2 &1 &2} \<guillemotleft>c\<guillemotright> ~ \<guillemotleft>d2\<guillemotright> {Q &1 &2}"
  shows "hoare {if e_fun e &2 then P1 &1 &2 else P2 &1 &2}
                  \<guillemotleft>c\<guillemotright> ~ if (\<guillemotleft>e\<guillemotright>) \<guillemotleft>d1\<guillemotright> else \<guillemotleft>d2\<guillemotright>
               {Q &1 &2}"
apply (rule rcase_rule[where f="\<lambda>m1 m2. e_fun e m2"])
apply (case_tac x, auto)
 apply (rule iftrue_rule_right)
  apply (rule rconseq_rule[where P'=P1 and Q'=Q], auto simp: assms)[2]
apply (rule iffalse_rule_right)
 by (rule rconseq_rule[where P'=P2 and Q'=Q], auto simp: assms)

lemma rif_rule:
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> e_fun e1 m1 = e_fun e2 m2"
  assumes "hoare {P &1 &2 \<and> e_fun e1 &1 \<and> e_fun e2 &2} \<guillemotleft>then1\<guillemotright> ~ \<guillemotleft>then2\<guillemotright> {Q &1 &2}"
  assumes "hoare {P &1 &2 \<and> \<not> e_fun e1 &1 \<and> \<not> e_fun e2 &2} \<guillemotleft>else1\<guillemotright> ~ \<guillemotleft>else2\<guillemotright> {Q &1 &2}"
  shows "hoare {P &1 &2} if (\<guillemotleft>e1\<guillemotright>) \<guillemotleft>then1\<guillemotright> else \<guillemotleft>else1\<guillemotright> ~ if (\<guillemotleft>e2\<guillemotright>) \<guillemotleft>then2\<guillemotright> else \<guillemotleft>else2\<guillemotright> {Q &1 &2}"
unfolding rhoare_untyped apply simp
apply (rule rif_rule)
using assms unfolding rhoare_untyped by auto

lemma rwhile_rule:
  assumes hoare: "hoare {I &1 &2 \<and> e_fun e1 &1} \<guillemotleft>p1\<guillemotright> ~ \<guillemotleft>p2\<guillemotright> {I &1 &2}"
      and PI: "\<And>m1 m2. P m1 m2 \<Longrightarrow> I m1 m2"
      and Ieq: "\<And>m1 m2. I m1 m2 \<Longrightarrow> e_fun e1 m1 \<longleftrightarrow> e_fun e2 m2"
      and IQ: "\<And>m1 m2. \<not> e_fun e1 m1 \<Longrightarrow> \<not> e_fun e2 m2 \<Longrightarrow> I m1 m2 \<Longrightarrow> Q m1 m2"
  shows "hoare {P &1 &2} while (\<guillemotleft>e1\<guillemotright>) \<guillemotleft>p1\<guillemotright> ~ while (\<guillemotleft>e2\<guillemotright>) \<guillemotleft>p2\<guillemotright> {Q &1 &2}"
unfolding rhoare_untyped apply simp
apply (rule rwhile_rule[where I=I])
using assms unfolding rhoare_untyped by auto

lemma rtrans_rule:
  assumes p:"\<And>m1 m2. P m1 m2 \<Longrightarrow> \<exists>m. P1 m1 m \<and> P2 m m2"
      and q:"\<And>m1 m2 m. Q1 m1 m \<Longrightarrow> Q2 m m2 \<Longrightarrow> Q m1 m2"
      and rhl1: "hoare {P1 &1 &2} \<guillemotleft>c1\<guillemotright> ~ \<guillemotleft>c\<guillemotright> {Q1 &1 &2}"
      and rhl2: "hoare {P2 &1 &2} \<guillemotleft>c\<guillemotright> ~ \<guillemotleft>c2\<guillemotright> {Q2 &1 &2}"
  shows "hoare {P &1 &2} \<guillemotleft>c1\<guillemotright> ~ \<guillemotleft>c2\<guillemotright> {Q &1 &2}"
unfolding rhoare_untyped
apply (rule rtrans_rule[of _ P1 P2 Q1 Q2])
using assms unfolding rhoare_untyped by auto



lemma rtrans3_rule:
  assumes p:"\<And>m1 m2. P m1 m2 \<Longrightarrow> \<exists>m m'. P1 m1 m \<and> P2 m m' \<and> P3 m' m2"
      and q:"\<And>m1 m2 m m'. Q1 m1 m \<Longrightarrow> Q2 m m' \<Longrightarrow> Q3 m' m2 \<Longrightarrow> Q m1 m2"
      and rhl1: "hoare {P1 &1 &2} \<guillemotleft>c1\<guillemotright> ~ \<guillemotleft>c2\<guillemotright> {Q1 &1 &2}"
      and rhl2: "hoare {P2 &1 &2} \<guillemotleft>c2\<guillemotright> ~ \<guillemotleft>c3\<guillemotright> {Q2 &1 &2}"
      and rhl3: "hoare {P3 &1 &2} \<guillemotleft>c3\<guillemotright> ~ \<guillemotleft>c4\<guillemotright> {Q3 &1 &2}"
  shows "hoare {P &1 &2} \<guillemotleft>c1\<guillemotright> ~ \<guillemotleft>c4\<guillemotright> {Q &1 &2}"
proof -
  define Q12 where "Q12 \<equiv> \<lambda>m1 m'. \<exists>m. Q1 m1 m \<and> Q2 m m'"
  define P12 where "P12 \<equiv> \<lambda>m1 m'. \<exists>m. P1 m1 m \<and> P2 m m'"
  have rhl12: "rhoare P12 c1 c3 Q12"
    apply (rule rtrans_rule[OF _ _ rhl1 rhl2])
    unfolding P12_def Q12_def by auto
  show ?thesis
    apply (rule rtrans_rule[OF _ _ rhl12 rhl3])
    unfolding P12_def Q12_def
     using p close metis
    using q by metis
qed


lemma seq_assoc_left_rule: 
  assumes "hoare {P &1 &2} \<guillemotleft>a\<guillemotright>;\<guillemotleft>b\<guillemotright>;\<guillemotleft>c\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {R &1 &2}"
  shows "hoare {P &1 &2} \<guillemotleft>a\<guillemotright>;{\<guillemotleft>b\<guillemotright>;\<guillemotleft>c\<guillemotright>} ~ \<guillemotleft>d\<guillemotright> {R &1 &2}"
using assms denotation_seq_assoc rhoare_def by auto

lemma seq_assoc_right_rule: 
  assumes "hoare {P &1 &2} \<guillemotleft>d\<guillemotright> ~ \<guillemotleft>a\<guillemotright>;\<guillemotleft>b\<guillemotright>;\<guillemotleft>c\<guillemotright> {R &1 &2}"
  shows "hoare {P &1 &2} \<guillemotleft>d\<guillemotright> ~ \<guillemotleft>a\<guillemotright>;{\<guillemotleft>b\<guillemotright>;\<guillemotleft>c\<guillemotright>} {R &1 &2}"
using assms denotation_seq_assoc rhoare_def by auto


lemma addskip_left_rule:
  assumes "hoare {P &1 &2} skip; \<guillemotleft>c\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {Q &1 &2}"
  shows "hoare {P &1 &2} \<guillemotleft>c\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {Q &1 &2}"
  using assms unfolding rhoare_def denotation_seq_skip by simp

lemma addskip_right_rule:
  assumes "hoare {P &1 &2} \<guillemotleft>c\<guillemotright> ~ skip; \<guillemotleft>d\<guillemotright> {Q &1 &2}"
  shows "hoare {P &1 &2} \<guillemotleft>c\<guillemotright> ~ \<guillemotleft>d\<guillemotright> {Q &1 &2}"
  using assms unfolding rhoare_def denotation_seq_skip by simp

(* Ordering of subgoals for certain tactics *)
lemma seq_rule_lastfirst_left:
  fixes P Q R c d e
  assumes "hoare {Q &1 &2} \<guillemotleft>d\<guillemotright> ~ skip {R &1 &2}" and "hoare {P &1 &2} \<guillemotleft>c\<guillemotright> ~ \<guillemotleft>e\<guillemotright> {Q &1 &2}"
  shows "hoare {P &1 &2} \<guillemotleft>c\<guillemotright>;\<guillemotleft>d\<guillemotright> ~ \<guillemotleft>e\<guillemotright> {R &1 &2}"
proof -
  have "hoare {P &1 &2} \<guillemotleft>c\<guillemotright>;\<guillemotleft>d\<guillemotright> ~ \<guillemotleft>e\<guillemotright>;skip {R &1 &2}"
    apply (rule rseq_rule) using assms by simp_all
  thus ?thesis
    unfolding rhoare_def denotation_skip_seq by assumption
qed

(* Ordering of subgoals for certain tactics *)
lemma seq_rule_lastfirst_right:
  fixes P Q R c d e
  assumes "hoare {Q &1 &2} skip ~ \<guillemotleft>d\<guillemotright> {R &1 &2}" and "hoare {P &1 &2} \<guillemotleft>e\<guillemotright> ~ \<guillemotleft>c\<guillemotright> {Q &1 &2}"
  shows "hoare {P &1 &2} \<guillemotleft>e\<guillemotright> ~ \<guillemotleft>c\<guillemotright>;\<guillemotleft>d\<guillemotright> {R &1 &2}"
proof -
  have "hoare {P &1 &2} \<guillemotleft>e\<guillemotright>;skip ~ \<guillemotleft>c\<guillemotright>;\<guillemotleft>d\<guillemotright> {R &1 &2}"
    apply (rule rseq_rule) using assms by simp_all
  thus ?thesis
    unfolding rhoare_def denotation_skip_seq by assumption
qed

(*
definition "assign_local_vars_typed locals (pargs::'a::procargs procargvars) (args::'a procargs)
  = Abs_program (assign_local_vars locals (mk_procargvars_untyped pargs) (mk_procargs_untyped args))"

lemma assign_local_vars_typed_simp1 [simp]: 
  "assign_local_vars_typed locals (procargvars_add p pargs) (procargs_add e args) = 
   seq (assign_local_vars_typed locals pargs args) (assign p e)"
using[[simp_trace_new]]
unfolding assign_local_vars_typed_def seq_def assign_def 
apply simp
find_theorems "mk_procargvars_untyped (procargvars_add _ _)"
apply (subst Abs_program_inverse, auto intro!: well_typed_assign_local_vars)
by (subst Abs_program_inverse, auto)
*)


(*
lemma assign_local_vars_typed_simp2 [simp]: 
  "assign_local_vars_typed (mk_variable_untyped x#locals) procargvars_empty procargs_empty = 
   seq (assign_local_vars_typed locals procargvars_empty procargs_empty) (assign x (const_expression default))"
      unfolding assign_local_vars_typed_def seq_def assign_def 
      apply (tactic "cong_tac @{context} 1", auto)
      close (subst Abs_program_inverse, auto intro!: well_typed_assign_local_vars)
      apply (subst Abs_program_inverse, auto simp: const_expression_def const_expression_untyped_def)
      unfolding mk_expression_untyped_def e_fun_def e_vars_def
      apply (subst Abs_expression_inverse) apply auto
      apply (subst Abs_expression_inverse) by auto

lemma assign_local_vars_typed_simp3 [simp]: 
  "assign_local_vars_typed [] procargvars_empty procargs_empty = Lang_Typed.skip"
unfolding assign_local_vars_typed_def skip_def by simp
*)


definition "assign_default_typed locals = Abs_program (assign_default locals)"

definition "assign_default_typed_aux p0 vs = Abs_program (foldl (\<lambda>p v. Seq p (Assign (pattern_1var v) 
                      (const_expression_untyped (vu_type v) (t_default (vu_type v))))) (Rep_program p0) vs)"

lemma assign_default_typed_aux: "assign_default_typed vs = assign_default_typed_aux Lang_Typed.skip vs"
  unfolding assign_default_typed_aux_def assign_default_def assign_default_typed_def
  by auto

lemma assign_default_typed_aux_cons: "assign_default_typed_aux p0 (mk_variable_untyped v # vs) = 
  assign_default_typed_aux (seq p0 (assign (variable_pattern v) (const_expression default))) vs"
  unfolding assign_default_typed_def assign_default_typed_aux_def assign_default_def seq_def
    assign_def variable_pattern_def mk_expression_untyped_const_expression
  apply simp
  apply (subst Abs_program_inverse)
   using assign_default_def assign_default_welltyped close auto
  apply (subst Abs_program_inverse)
   close (simp add: embedding_Type eu_type_const_expression_untyped)
  apply (subst Abs_pattern_inverse)
   by auto

lemma assign_default_typed_aux_nil: "assign_default_typed_aux p0 [] = p0"
  unfolding assign_default_typed_def assign_default_typed_aux_def assign_default_def skip_def 
  by (auto simp: Rep_program_inverse)


(* 
definition "assign_default_typed_rev vs = assign_default_typed (rev vs)"
lemma assign_default_typed_rev: "assign_default_typed vs = assign_default_typed_rev (rev vs)"
unfolding assign_default_typed_rev_def by auto

lemma "assign_default_typed ([mk_variable_untyped a,mk_variable_untyped b,mk_variable_untyped c]) =
  PROGRAM [ skip; a:=default; b:=default; c:=default ]"
  unfolding assign_default_typed_def assign_default_def program_def seq_def assign_def
      variable_pattern_def mk_expression_untyped_const_expression 
  apply (subst Abs_program_inverse, tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  apply (subst Abs_pattern_inverse, tactic \<open>Skip_Proof.cheat_tac @{context} 1\<close>)+
  by simp

lemma assign_default_typed_rev_cons: "assign_default_typed_rev (mk_variable_untyped v # vs) = seq (assign_default_typed_rev vs) (assign (variable_pattern v) (const_expression default))"
  unfolding assign_default_typed_def assign_default_typed_rev_def assign_default_def seq_def
    assign_def variable_pattern_def mk_expression_untyped_const_expression
  apply simp
  apply (subst Abs_program_inverse)
   using assign_default_def assign_default_welltyped close auto
  apply (subst Abs_program_inverse)
   close (simp add: embedding_Type eu_type_const_expression_untyped)
  apply (subst Abs_pattern_inverse)
   by auto

lemma assign_default_typed_rev_nil: "assign_default_typed_rev [] = Lang_Typed.skip"
  unfolding assign_default_typed_def assign_default_typed_rev_def assign_default_def skip_def
  by auto
*)


(* If the number of subgoals change, inline_rule_conditions_tac must be adapted accordingly *)
lemma callproc_rule:
  fixes p::"('a::prog_type,'b::prog_type) procedure" and x::"'b pattern" and args::"'a expression"
    and locals::"variable_untyped list" and V::"variable_untyped set"
    and non_parg_locals::"variable_untyped list"
  defines "body == p_body p"
  defines "ret == p_return p"
  defines "pargs == p_arg p"
(*  defines "GL == {x. vu_global x}" *)
  assumes proc_locals: "set(local_vars body) \<union> filter_local (set(p_vars pargs) \<union> set(e_vars ret)) \<subseteq> set locals"
  assumes locals_local: "filter_global (set locals) = {}"
  assumes localsV: "V \<inter> set locals \<subseteq> set (p_vars x)"
  assumes proc_globals: "filter_global (set(vars body) \<union> set(e_vars ret)) \<subseteq> V"
  assumes argvarsV: "set(e_vars args) \<subseteq> V"
  assumes non_parg_locals: "set non_parg_locals = set locals - set (p_vars pargs)"

  defines "unfolded == seq (seq (seq (assign pargs args) (assign_default_typed non_parg_locals)) body) (assign x ret)"
  shows "obs_eq' V (callproc x p args) unfolded"
proof -
  (*def GL == "{x. vu_global x} :: variable_untyped set"
  have fl_GL: "\<And>X. filter_local X = X - GL"
    unfolding GL_def filter_local_def by auto
  have fg_GL: "\<And>X. filter_global X = X \<inter> GL"
    unfolding GL_def filter_global_def by auto*)
  define body' where "body' \<equiv> Rep_program (p_body p)"
  define pargs' where "pargs' \<equiv> Rep_pattern (p_arg p)"
  define ret' where "ret' \<equiv> mk_expression_untyped (p_return p)"
  define p' where "p' \<equiv> Proc body' pargs' ret'"
  have p': "mk_procedure_untyped p = p'"
    unfolding mk_procedure_untyped_def p'_def body'_def pargs'_def ret'_def ..
  define x' where "x' \<equiv> Rep_pattern x"
  define args' where "args' \<equiv> mk_expression_untyped args"
  have callproc: "Rep_program (callproc x p args) == CallProc x' p' args'"
    unfolding Rep_callproc x'_def[symmetric] p' args'_def[symmetric] by assumption
  define unfolded' where "unfolded' \<equiv> Seq (Seq (Seq (Assign pargs' args') (assign_default non_parg_locals)) body')
                           (Assign x' ret')"
  have assign: "Rep_program (assign_default_typed locals) == assign_default locals"
      unfolding assign_default_typed_def 
      apply (subst Abs_program_inverse, auto)
      by (rule assign_default_welltyped)
  have unfolded: "Rep_program unfolded = unfolded'"
    unfolding unfolded'_def unfolded_def program_def pargs'_def pargs_def args'_def
    Rep_seq assign body'_def body_def Rep_assign ret_def
    x'_def[symmetric] ret'_def[symmetric] assign_default_typed_def
   apply (subst Abs_program_inverse)
   using assign_default_welltyped by auto
  have fl_loc_var: "\<And>p. set (local_vars p) = filter_local (set (vars p))"
    unfolding local_vars_def filter_local_def by auto
  have fl_union: "\<And>A B. filter_local (A \<union> B) = filter_local A \<union> filter_local B"
    unfolding filter_local_def by auto
  have proc_locals': "filter_local (set (vars (p_body p)) \<union> set (p_vars (p_arg p)) \<union> set (eu_vars (mk_expression_untyped (p_return p)))) \<subseteq> set locals"
    using proc_locals unfolding fl_union pargs_def ret_def body_def fl_loc_var by auto
  show "obs_eq' V (callproc x p args) unfolded"
    unfolding obs_eq'_def obs_eq_obs_eq_untyped callproc unfolded unfolded'_def p'_def 
    apply (rule callproc_rule) 
    unfolding body'_def x'_def vars_def[symmetric] e_vars_def[symmetric] p_vars_def[symmetric] pargs'_def ret'_def args'_def 
    using assms proc_locals' local_vars_def by auto
qed

(* Outputs the list of parameters of callproc_rule, ordered like the arguments to Drule.instantiate' *)
ML {* Term.add_vars (Thm.prop_of @{thm callproc_rule}) [] |> rev |> map Var |> map (Syntax.string_of_term @{context}) |> String.concatWith "\n" |> writeln *}

(* If the subgoals change, inline_rule_conditions_tac must be adapted accordingly *)
(* locals and non_parg_locals have to be already renamed *)
lemma callproc_rule_renamed:
  fixes p::"('a::prog_type,'b::prog_type) procedure" and x::"'b pattern" and args::"'a expression"
    and locals::"variable_untyped list" and V::"variable_untyped set"
    and non_parg_locals::"variable_untyped list"
    and renaming::"variable_name_renaming"

  defines "body == p_body p"
  defines "ret == p_return p"
  defines "pargs == p_arg p"

  assumes proc_locals: "local_variable_name_renaming renaming ` (set(local_vars body) \<union> filter_local (set(p_vars pargs) \<union> set(e_vars ret))) \<subseteq> set locals"
  assumes locals_local: "filter_global (set locals) = {}"
  assumes localsV: "V \<inter> set locals \<subseteq> set (p_vars x)"
  assumes proc_globals: "local_variable_name_renaming renaming ` (filter_global(set(vars body) \<union> set(e_vars ret))) \<subseteq> V"
  assumes argvarsV: "set(e_vars args) \<subseteq> V"
  assumes non_parg_locals: "set non_parg_locals = set locals - local_variable_name_renaming renaming ` set (p_vars pargs)"

  defines "unfolded == seq (seq (seq (assign (rename_local_variables_pattern renaming pargs) args)
                                     (assign_default_typed non_parg_locals))
                                     (rename_local_variables renaming body))
                                     (assign x (rename_local_variables_expression renaming ret))"
  shows "obs_eq' V (callproc x p args) unfolded"
proof -
  define body' where "body' \<equiv> p_body (rename_local_variables_proc renaming p)"
  define ret' where "ret' \<equiv> p_return (rename_local_variables_proc renaming p)"
  define pargs' where "pargs' \<equiv> p_arg (rename_local_variables_proc renaming p)"
  define unfolded' where "unfolded' \<equiv> seq (seq (seq (assign pargs' args) (assign_default_typed non_parg_locals)) body') (assign x ret')"
  have filter_renaming: "\<And>X. filter_local (local_variable_name_renaming renaming ` X) = local_variable_name_renaming renaming ` filter_local X"
    unfolding filter_local_def using local_variable_name_renaming_global by auto
  have "unfolded = unfolded'"
    unfolding unfolded_def unfolded'_def pargs'_def pargs_def p_arg_rename_local_variables_proc
              body'_def body_def p_body_rename_local_variables_proc ret'_def ret_def
              p_ret_rename_local_variables_proc by simp
  have obseq: "obs_eq' V (callproc x (rename_local_variables_proc renaming p) args) unfolded'"
    unfolding unfolded'_def pargs'_def ret'_def body'_def
    apply (rule callproc_rule[where locals=locals])
    unfolding p_body_rename_local_variables_proc body_def[symmetric]
    unfolding p_arg_rename_local_variables_proc pargs_def[symmetric]
    unfolding p_ret_rename_local_variables_proc ret_def[symmetric]
    unfolding local_vars_rename_local_variables
    unfolding p_vars_rename_local_variables_pattern
    unfolding e_vars_rename_local_variables_expression
    unfolding vars_rename_local_variables 
    unfolding set_map
    using assms unfolding filter_local_def filter_global_def by auto
  hence obseq: "obs_eq' V (callproc x (rename_local_variables_proc renaming p) args) unfolded"
    unfolding `unfolded=unfolded'` by assumption
  then show ?thesis
    unfolding obs_eq'_def obs_eq_def rhoare_def denotation_callproc_rename_local_variables_proc 
    by assumption
qed

(* Outputs the list of parameters of callproc_rule, ordered like the arguments to Drule.instantiate' *)
ML {* Term.add_vars (Thm.prop_of @{thm callproc_rule_renamed}) [] |> rev |> map Var |> map (Syntax.string_of_term @{context}) |> String.concatWith "\n" |> writeln *}



(*
definition "blockassign (xs::'a::procargs procargvars) (es::'a procargs) == 
  Abs_program
  (fold 
  (\<lambda>(x,e) p. Seq p (Assign x e))
  (zip (mk_procargvars_untyped xs) (mk_procargs_untyped es))
  Skip)"


lemma callproc_equiv:
  fixes x p e
  defines "V_e == set [v. e \<leftarrow> mk_procargs_untyped e, v \<leftarrow> eu_vars e]"
  defines "V_p == set (vars (p_body p)) \<union> set (mk_procargvars_untyped (p_args p)) \<union> set (e_vars (p_return p))"
  assumes "V_p \<inter> V = {}" and "V_p \<inter> V_e = {}"
  shows "hoare {\<forall>x\<in>V. memory_lookup_untyped &1 x = memory_lookup_untyped &2 x} 
                  \<guillemotleft>callproc x p e\<guillemotright> ~ \<guillemotleft>blockassign (p_args p) e\<guillemotright>; \<guillemotleft>p_body p\<guillemotright>; x := \<guillemotleft>p_return p\<guillemotright>
               {\<forall>x\<in>V. memory_lookup_untyped &1 x = memory_lookup_untyped &2 x}"
*)

definition "obseq_context X C == (\<forall>c d. obs_eq X X c d \<longrightarrow> obs_eq X X (C c) (C d))"

lemma assertion_footprint_left_lookup: "mk_variable_untyped x \<in> X \<Longrightarrow> assertion_footprint_left X (\<lambda>m1 m2. memory_lookup m1 x)"
  unfolding assertion_footprint_left_def by auto
lemma assertion_footprint_right_lookup: "mk_variable_untyped x \<in> X \<Longrightarrow> assertion_footprint_right X (\<lambda>m1 m2. memory_lookup m2 x)"
  unfolding assertion_footprint_right_def by auto


lemma assertion_footprint_left_update:
  assumes "Y \<subseteq> insert (mk_variable_untyped x) X"
  assumes "assertion_footprint_left Y P"
  shows "assertion_footprint_left X (\<lambda>m m'. P (memory_update m x v) m')"
unfolding memory_update_def
apply (rule assertion_footprint_left_update_untyped)
using assms by auto

lemma assertion_footprint_right_update:
  assumes "Y \<subseteq> insert (mk_variable_untyped x) X"
  assumes "assertion_footprint_right Y P"
  shows "assertion_footprint_right X (\<lambda>m m'. P m (memory_update m' x v))"
unfolding memory_update_def
apply (rule assertion_footprint_right_update_untyped)
using assms by auto


lemma assertion_footprint_left_update_pattern:
  assumes "Y \<subseteq> X \<union> set (p_vars pat)"
  assumes "assertion_footprint_left Y P"
  shows "assertion_footprint_left X (\<lambda>m m'. P (memory_update_pattern m pat x) m')"
unfolding memory_update_pattern_def
apply (rule assertion_footprint_left_update_pattern_untyped)
using assms unfolding p_vars_def by auto

lemma assertion_footprint_right_update_pattern:
  assumes "Y \<subseteq> X \<union> set (p_vars pat)"
  assumes "assertion_footprint_right Y P"
  shows "assertion_footprint_right X (\<lambda>m m'. P m (memory_update_pattern m' pat x))"
unfolding memory_update_pattern_def
apply (rule assertion_footprint_right_update_pattern_untyped)
using assms unfolding p_vars_def by auto

lemma rskip_rule [simp]:
  assumes "\<forall>m m'. P m m' \<longrightarrow> Q m m'"
  shows "hoare {P &1 &2} skip ~ skip {Q &1 &2}"
  using assms by (simp add: rhoare_untyped RHL_Untyped.rskip_rule)

lemma rskip_rule_strict: "hoare {P &1 &2} skip ~ skip {P &1 &2}"
  by (simp add: rhoare_untyped RHL_Untyped.rskip_rule)

lemma obseq_context_as_rule:
  fixes X defines "eq == \<lambda>(m1::memory) m2::memory. \<forall>x::variable_untyped\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  assumes obseq: "obseq_context X C"
  assumes rh: "rhoare eq c d eq"
  shows "rhoare eq (C c) (C d) eq"
using assms unfolding obseq_context_def obs_eq_def eq_def by auto

lemma obseq_context_seq:                                        
  assumes "obseq_context X C1"
  assumes "obseq_context X C2"
  shows "obseq_context X (\<lambda>c. seq (C1 c) (C2 c))"
proof -
  define eq where "eq \<equiv> \<lambda>(m1::memory) m2::memory. \<forall>x::variable_untyped\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  note eq = eq_def[symmetric]
  {fix c d assume rh: "rhoare eq c d eq"
  have "rhoare eq (seq (C1 c) (C2 c)) (seq (C1 d) (C2 d)) eq"
    apply (rule rseq_rule[where Q=eq])
     apply (rule obseq_context_as_rule[OF assms(1), unfolded eq])
     close (fact rh)
    apply (rule obseq_context_as_rule[OF assms(2), unfolded eq])
    by (fact rh)}
  thus ?thesis
    unfolding obseq_context_def obs_eq_def eq_def by simp
qed

lemma obseq_context_ifte: 
  assumes C1: "obseq_context X C1"
  assumes C2: "obseq_context X C2"
  assumes vars: "set (e_vars e) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. ifte e (C1 c) (C2 c))"
proof -
  define eq where "eq \<equiv> \<lambda>(m1::memory) m2::memory. \<forall>x::variable_untyped\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  have foot: "\<And>m1 m2. eq m1 m2 \<Longrightarrow> e_fun e m1 = e_fun e m2" unfolding eq_def apply (rule e_fun_footprint) using vars by auto
  note eq = eq_def[symmetric]
  {fix c d assume rh: "rhoare eq c d eq"
  have "rhoare eq (ifte e (C1 c) (C2 c)) (ifte e (C1 d) (C2 d)) eq"
    apply (rule rif_rule)
      close (fact foot)
     apply (rule rconseq_rule[where P'=eq and Q'=eq]) close simp close simp
     apply (rule obseq_context_as_rule[OF C1, unfolded eq])
     close (fact rh)
    apply (rule rconseq_rule[where P'=eq and Q'=eq]) close simp close simp
    apply (rule obseq_context_as_rule[OF C2, unfolded eq])
    by (fact rh)}
  thus ?thesis
    unfolding obseq_context_def obs_eq_def eq_def by simp
qed

lemma obseq_context_while: 
  assumes C1: "obseq_context X C1"
  assumes vars: "set (e_vars e) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. Lang_Typed.while e (C1 c))"
proof -
  define eq where "eq \<equiv> \<lambda>m1 m2::memory. \<forall>x::variable_untyped\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  have foot: "\<And>m1 m2. eq m1 m2 \<Longrightarrow> e_fun e m1 = e_fun e m2" unfolding eq_def apply (rule e_fun_footprint) using vars by auto
  note eq = eq_def[symmetric]
  {fix c d assume rh: "rhoare eq c d eq"
  have "rhoare eq (Lang_Typed.while e (C1 c)) (Lang_Typed.while e (C1 d)) eq"
    apply (rule rwhile_rule[where I=eq])
       apply (rule rconseq_rule[where P'=eq and Q'=eq]) close simp close simp
       apply (rule obseq_context_as_rule[OF C1, unfolded eq])
       close (fact rh)
      using foot by auto}
  thus ?thesis
    unfolding obseq_context_def obs_eq_def eq_def by simp
qed


lemma self_obseq_vars:
  assumes vars: "set(vars c) \<subseteq> X"
  assumes YX: "Y \<subseteq> X"
  shows "obs_eq X Y c c"
unfolding obs_eq_obs_eq_untyped
apply (rule self_obseq_vars_untyped)
using assms unfolding vars_def by auto

lemma self_obs_eq_callproc:
  assumes YX: "Y \<subseteq> X \<union> set (p_vars x)"
  assumes bodyX: "set (vars (p_body p)) \<subseteq> X \<union> {x. \<not> vu_global x}"
  assumes retX: "set (e_vars (p_return p)) \<subseteq> X \<union> {x. \<not> vu_global x}"
  assumes argsX: "set (p_vars (p_arg p)) \<subseteq> X \<union> {x. \<not> vu_global x}"
  assumes aX: "set (e_vars y) \<subseteq> X"
  shows "obs_eq X Y (callproc x p y) (callproc x p y)"
proof -
  obtain body args ret where p: "mk_procedure_untyped p = Proc body args ret"
    using mk_procedure_untyped_def by blast
  hence p_body: "Rep_program (p_body p) = body"
    and p_return: "mk_expression_untyped (p_return p) = ret"
    and p_args: "Rep_pattern (p_arg p) = args"
    by (simp_all add: mk_procedure_untyped_def)
  show ?thesis
    unfolding obs_eq_obs_eq_untyped apply (simp add: p)
    apply (rule self_obs_eq_callproc_untyped)
        close (metis YX p_vars_def)
       using bodyX unfolding vars_def p_body close 
      using retX mk_expression_untyped_vars p_return close
     close (metis argsX p_args p_vars_def)
    by (simp add: aX)
qed

lemma obseq_context_empty: 
  shows "obseq_context X (\<lambda>c. c)"
unfolding obseq_context_def by simp


lemma obseq_context_assign: 
  assumes "set (p_vars x) \<subseteq> X"
  assumes "set (e_vars e) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. assign x e)"
unfolding obseq_context_def apply rule+ apply (thin_tac _)
apply (rule self_obseq_vars)
using assms by auto

lemma obseq_context_skip: "obseq_context X (\<lambda>c. Lang_Typed.skip)"
  unfolding obseq_context_def apply auto unfolding obs_eq_def
  by (simp add: rhoare_untyped RHL_Untyped.rskip_rule)

lemma obseq_context_sample: 
  assumes "set (p_vars x) \<subseteq> X"
  assumes "set (e_vars e) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. sample x e)"
unfolding obseq_context_def apply rule+ apply (thin_tac _)
apply (rule self_obseq_vars)
using assms by auto

lemma obseq_context_callproc_allglobals: 
  fixes X' defines "X == X' \<union> Collect vu_global"
  assumes "set (p_vars x) \<subseteq> X"
  assumes "set (e_vars a) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. callproc x p a)"
unfolding obseq_context_def apply rule+ apply (thin_tac _)
unfolding obs_eq_obs_eq_untyped
apply (rule self_obseq_vars_untyped)
using assms unfolding p_vars_def 
by (auto simp: vars_proc_untyped_global)


lemma hoare_obseq_replace_ctx: 
  assumes C: "obseq_context X C"
  assumes Q: "assertion_footprint X Q"
  assumes eq: "obs_eq' X c d"
  assumes hoare: "hoare {P &m} \<guillemotleft>C d\<guillemotright> {Q &m}"
  shows "hoare {P &m} \<guillemotleft>C c\<guillemotright> {Q &m}"
proof -
  let ?eq = "\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  let ?c = "Rep_program (C c)"
  let ?d = "Rep_program (C d)"
  have "obs_eq' X (C c) (C d)"
    unfolding obs_eq'_def obs_eq_def
    apply (rule obseq_context_as_rule[OF C])
    using eq unfolding obs_eq'_def obs_eq_def by assumption
  hence "obs_eq_untyped X X ?c ?d"
    by (simp add: obs_eq'_def obs_eq_obs_eq_untyped)
  moreover have "hoare_untyped P ?d Q"
    using hoare hoare_untyped by auto
  ultimately have "hoare_untyped P ?c Q"
    using Q by (rule hoare_obseq_replace_untyped[rotated])
  thus ?thesis unfolding hoare_untyped by assumption
qed

lemma rhoare_left_obseq_replace: 
  assumes ctx: "obseq_context X C"
  assumes foot: "assertion_footprint_left X Q"
  assumes obseq: "obs_eq' X c d"
  assumes rhoare: "hoare {P &1 &2} \<guillemotleft>C d\<guillemotright> ~ \<guillemotleft>c'\<guillemotright> {Q &1 &2}"
  shows "hoare {P &1 &2} \<guillemotleft>C c\<guillemotright> ~ \<guillemotleft>c'\<guillemotright> {Q &1 &2}"
proof -
  have obseqCc: "obs_eq' X (C c) (C d)"
    using obseq ctx unfolding obseq_context_def obs_eq'_def obs_eq_def by simp
  note obseqCc' = obseqCc[unfolded obs_eq'_def obs_eq_def]
  show ?thesis
    apply (rule rtrans_rule[OF _ _ obseqCc' rhoare])
     close
    using foot by (simp add: assertion_footprint_left_def)
qed

lemma rhoare_right_obseq_replace: 
  assumes "obseq_context X C"
  assumes "assertion_footprint_right X Q"
  assumes "obs_eq' X c d"
  assumes "hoare {P &1 &2}  \<guillemotleft>c'\<guillemotright> ~ \<guillemotleft>C d\<guillemotright> {Q &1 &2}"
  shows "hoare {P &1 &2}  \<guillemotleft>c'\<guillemotright> ~ \<guillemotleft>C c\<guillemotright> {Q &1 &2}"
apply (rule rsymmetric_rule)
apply (rule rhoare_left_obseq_replace[where C=C])
   close (fact assms(1))
  using assms(2) unfolding assertion_footprint_left_def assertion_footprint_right_def close auto
 close (fact assms(3))
apply (rule rsymmetric_rule)
by (fact assms(4))

lemma program_footprint_vars: "program_footprint (set(vars p)) p"
  using program_untyped_footprint_vars
  unfolding program_footprint_def program_untyped_footprint_def vars_def denotation_def.


lemma seq_swap2:
  assumes "set (vars a) \<inter> set (write_vars b) = {}"
  assumes "set (vars b) \<inter> set (write_vars a) = {}"
  shows "denotation (seq a b) = denotation (seq b a)"
proof -
  define A where "A \<equiv> set(vars a)"
  define B where "B \<equiv> set(vars b)"
  define R where "R \<equiv> UNIV - set(write_vars a) - set(write_vars b)"
  have "program_readonly R a"
    using R_def denotation_readonly_def program_readonly_def program_readonly_write_vars by (auto,blast) 
  moreover have "program_readonly R b"
    using R_def denotation_readonly_def program_readonly_def program_readonly_write_vars by (auto,blast)
  moreover have "program_footprint A a"
    using A_def program_footprint_vars by auto
  moreover have "program_footprint B b"
    using B_def program_footprint_vars by auto
  moreover have ABR: "A\<inter>B\<subseteq>R"
    unfolding A_def B_def R_def using assms by auto
  ultimately show ?thesis
    by (rule seq_swap)
qed    

lemma frame_rule: 
  assumes foot1: "assertion_footprint_left X R" and foot2: "assertion_footprint_right Y R"
  assumes ro1: "program_readonly X p1" and ro2: "program_readonly Y p2"
  assumes rhoare: "rhoare P p1 p2 Q"
  shows "rhoare (\<lambda>m1 m2. P m1 m2 \<and> R m1 m2) p1 p2 (\<lambda>m1 m2. Q m1 m2 \<and> R m1 m2)"
unfolding rhoare_untyped
apply (rule frame_rule_untyped)
using assms unfolding program_readonly_def program_untyped_readonly_def denotation_def rhoare_untyped by auto


lemma callproc_equiv: 
  assumes globals_V1: "set (vars_proc_global f) \<subseteq> V1"
  assumes V2V1: "V2 \<subseteq> V1"
  assumes x1V2: "set (p_vars x1) \<inter> V2 = {}"
  assumes x2V2: "set (p_vars x2) \<inter> V2 = {}"
  shows "rhoare (\<lambda>m1 m2. (\<forall>v\<in>V1. memory_lookup_untyped m1 v = memory_lookup_untyped m2 v)
                      \<and> e_fun e1 m1 = e_fun e2 m2)
                   (callproc x1 f e1) (callproc x2 f e2)
                (\<lambda>m1 m2. (\<forall>v\<in>V2. memory_lookup_untyped m1 v = memory_lookup_untyped m2 v)
                      \<and> memory_pattern_related x1 x2 m1 m2)"
proof (rule rhoareI, goal_cases)
case (1 m1 m2)  
  hence eq_m1_m2: "memory_lookup_untyped m1 v = memory_lookup_untyped m2 v"
        if "v\<in>V1" for v 
    using that by auto
  from 1 have e1e2: "e_fun e1 m1 = e_fun e2 m2" by simp
  define argval where "argval \<equiv> e_fun e1 m1"
  define m1a where "m1a \<equiv> init_locals m1"
  define m1b where "m1b \<equiv> memory_update_pattern m1a (p_arg f) argval"
  define m2a where "m2a \<equiv> init_locals m2"
  define m2b where "m2b \<equiv> memory_update_pattern m2a (p_arg f) argval"

  have eq_m12a: "memory_lookup_untyped m1a v = memory_lookup_untyped m2a v" if "v\<in>V1" for v 
    using that eq_m1_m2 by (simp add: Rep_init_locals m1a_def m2a_def)
  have eq_m12a_loc: "memory_lookup_untyped m1a v = memory_lookup_untyped m2a v" if "\<not> vu_global v" for v 
    using that by (simp add: Rep_init_locals m1a_def m2a_def)
  have eq_m12b_V1: "memory_lookup_untyped m1b v = memory_lookup_untyped m2b v" if "v\<in>V1" for v 
    unfolding m1b_def m2b_def memory_update_pattern_def using that eq_m12a
    by (metis lookup_memory_update_untyped_pattern_getter memory_lookup_update_pattern_notsame)
  have eq_m12b_loc: "memory_lookup_untyped m1b v = memory_lookup_untyped m2b v" if "\<not> vu_global v" for v 
    unfolding m1b_def m2b_def memory_update_pattern_def using eq_m12a_loc that
    by (metis lookup_memory_update_untyped_pattern_getter memory_lookup_update_pattern_notsame)
(*   have "memory_lookup_untyped m1b v = memory_lookup_untyped m2b v" if "v \<in> set(p_vars(p_arg f))" for v 
    using that by auto *)

  define V1loc where "V1loc \<equiv> V1 \<union> {x. \<not> vu_global x}"

  have vars_V1loc: "set(vars(p_body f)) \<subseteq> V1loc"
    using globals_V1 unfolding vars_proc_global_def V1loc_def by auto
  with eq_m12b_V1 eq_m12b_loc
  have eq_m12b: "memory_lookup_untyped m1b v = memory_lookup_untyped m2b v" if "v \<in> V1loc" for v
    using that V1loc_def by auto

  have "obs_eq V1loc V1loc (p_body f) (p_body f)"
    apply (rule self_obseq_vars)
    using vars_V1loc by (simp_all add: vars_def) 
  
  then obtain \<mu> where \<mu>fst: "apply_to_distr fst \<mu> = denotation (p_body f) m1b"
                  and \<mu>snd: "apply_to_distr snd \<mu> = denotation (p_body f) m2b"
                  and \<mu>post: "\<And>m1' m2' x. (m1',m2') \<in> support_distr \<mu> \<Longrightarrow> x\<in>V1loc \<Longrightarrow> 
                                memory_lookup_untyped m1' x = memory_lookup_untyped m2' x"
    unfolding obs_eq_def rhoare_def
    using eq_m12b by blast 

  define finalize where "finalize \<equiv> \<lambda>m x. \<lambda>m'. let res = e_fun (p_return f) m'; m' = restore_locals m m' in memory_update_pattern m' x res"

  define \<mu>' where "\<mu>' \<equiv> apply_to_distr (\<lambda>(m1',m2'). (finalize m1 x1 m1', finalize m2 x2 m2')) \<mu>"

  have "apply_to_distr fst \<mu>' = apply_to_distr (\<lambda>m1'. finalize m1 x1 m1') (apply_to_distr fst \<mu>)"
    unfolding \<mu>'_def by (simp add: split_def)
  also have "\<dots> = apply_to_distr (\<lambda>m1'. finalize m1 x1 m1') (denotation (p_body f) m1b)"
    using \<mu>fst by simp
  also have "\<dots> = denotation (callproc x1 f e1) m1"
    unfolding argval_def m1a_def m1b_def finalize_def
    apply (subst denotation_callproc) by auto
  finally have \<mu>'fst: "apply_to_distr fst \<mu>' = denotation (callproc x1 f e1) m1" by assumption

  have "apply_to_distr snd \<mu>' = apply_to_distr (\<lambda>m2'. finalize m2 x2 m2') (apply_to_distr snd \<mu>)"
    unfolding \<mu>'_def by (simp add: split_def)
  also have "\<dots> = apply_to_distr (\<lambda>m2'. finalize m2 x2 m2') (denotation (p_body f) m2b)"
    using \<mu>snd by simp
  also have "\<dots> = denotation (callproc x2 f e2) m2"
    unfolding argval_def m2a_def m2b_def finalize_def e1e2
    apply (subst denotation_callproc) by auto
  finally have \<mu>'snd: "apply_to_distr snd \<mu>' = denotation (callproc x2 f e2) m2"
    by assumption

  have \<mu>'post: "\<And>x. x\<in>V2 \<Longrightarrow> memory_lookup_untyped m1' x = memory_lookup_untyped m2' x"
   and \<mu>'post2: "memory_pattern_related x1 x2 m1' m2'"
               if supp: "(m1',m2') \<in> support_distr \<mu>'" 
               for m1' m2'
  proof -
    from supp obtain m1'' m2'' where 
        m1': "m1' = finalize m1 x1 m1''" and m2': "m2' = finalize m2 x2 m2''" and "(m1'',m2'') \<in> support_distr \<mu>"
        unfolding \<mu>'_def by auto
    hence eq_m12'': "\<And>x. x\<in>V1loc \<Longrightarrow> memory_lookup_untyped m1'' x = memory_lookup_untyped m2'' x"
      using \<mu>post by simp

    have ret_V1loc: "set (e_vars (p_return f)) \<subseteq> V1loc"
      unfolding V1loc_def using globals_V1 unfolding vars_proc_global_def by auto
    have ret12: "e_fun (p_return f) m1'' = e_fun (p_return f) m2''"
      apply (rule e_fun_footprint)
      apply (rule eq_m12'') 
      using ret_V1loc by auto

    show "memory_pattern_related x1 x2 m1' m2'"
      apply (rule memory_pattern_relatedI)
      unfolding m1' m2' finalize_def ret12 by auto

    show "memory_lookup_untyped m1' x = memory_lookup_untyped m2' x" if "x\<in>V2" for x
    proof -
      define ret where "ret \<equiv> e_fun (p_return f) m1''"
      define m1l where "m1l \<equiv> restore_locals m1 m1''"
      define m2l where "m2l \<equiv> restore_locals m2 m2''"
      have "m1' = memory_update_pattern m1l x1 ret"
        unfolding ret_def m1' finalize_def m1l_def by auto
      have "m2' = memory_update_pattern m2l x2 ret"
        unfolding ret_def m2' finalize_def m2l_def ret12 by auto

      have xx1: "x \<notin> set (p_vars x1)" and xx2: "x \<notin> set (p_vars x2)"
        using x1V2 x2V2 that by auto

      have "memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
        using V2V1 eq_m1_m2 that by blast
      moreover have "memory_lookup_untyped m1'' x = memory_lookup_untyped m2'' x"
        using V1loc_def V2V1 eq_m12'' that by auto
      ultimately have "memory_lookup_untyped (restore_locals m1 m1'') x = memory_lookup_untyped (restore_locals m2 m2'') x" 
        unfolding Rep_restore_locals by simp

      then have "memory_lookup_untyped (memory_update_pattern (restore_locals m1 m1'') x1 ret) x =
                 memory_lookup_untyped (memory_update_pattern (restore_locals m2 m2'') x2 ret) x"
        unfolding memory_update_pattern_def
        apply (subst memory_lookup_update_pattern_notsame) close (metis p_vars_def xx1)
        apply (subst memory_lookup_update_pattern_notsame) close (metis p_vars_def xx2)
        by assumption
      then show ?thesis
        unfolding m1' m2' finalize_def ret_def[symmetric] ret12[symmetric] by simp
    qed
  qed

  from \<mu>'fst \<mu>'snd \<mu>'post \<mu>'post2 show ?case
    apply (rule_tac exI[of _ \<mu>']) by auto
qed 



lemma call_rule:
  fixes globals_f1 globals_f2 and x1::"'x1::prog_type pattern" and x2::"'x2::prog_type pattern" 
    and y1::"'y1::prog_type expression" and y2::"'y2::prog_type expression" 
    and res1::"'x1 variable" and res2::"'x2 variable" and A B P Q 
  assumes globals_f1: "set(write_vars_proc_global f1) \<subseteq> set globals_f1"
  assumes globals_f2: "set(write_vars_proc_global f2) \<subseteq> set globals_f2"
  assumes args1_nin_f1: "mk_variable_untyped args1 \<notin> set (vars_proc_global f1)"
  assumes args2_nin_f2: "mk_variable_untyped args2 \<notin> set (vars_proc_global f2)"
  assumes footQ1: "assertion_footprint_left (-{mk_variable_untyped args1}) Q"
  assumes footQ2: "assertion_footprint_right (-{mk_variable_untyped args2}) Q"
  assumes f1f2: "rhoare P
              (callproc (variable_pattern res1) f1 (var_expression args1))
              (callproc (variable_pattern res2) f2 (var_expression args2))
              Q"
  defines "QB == (\<lambda>m1 m2. (\<forall>gL gR xL xR x'L x'R. 
                    gL \<in> t_domain (pu_type (list_pattern_untyped globals_f1))
                \<longrightarrow> gR \<in> t_domain (pu_type (list_pattern_untyped globals_f2))
                \<longrightarrow> Q (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f1) gL) (list_pattern_untyped (p_vars x1)) x'L) res1 xL)
                       (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f2) gR) (list_pattern_untyped (p_vars x2)) x'R) res2 xR)
                \<longrightarrow> B (memory_update_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f1) gL) x1 xL)
                      (memory_update_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f2) gR) x2 xR)))"
  defines "C == (\<lambda>m1 m2. P (memory_update m1 args1 (e_fun y1 m1)) (memory_update m2 args2 (e_fun y2 m2)) \<and> QB m1 m2)"
  assumes p1p2: "rhoare A p1 p2 C"
  shows "rhoare A (seq p1 (callproc x1 f1 y1)) (seq p2 (callproc x2 f2 y2)) B"
proof -

(* Proof plan: 

- Show:  rhoare    P{args/y}  (callproc x=f(y))  Q{x/res}    (substitution)   \<longrightarrow>  rhoareP'Q'
- Show:  footprint QB   disjoint of   callproc x=f(y)
- Show:  rhoare    C=P{args/y}\<and>QB     (callproc x=f(y))   Q{res/x}\<and>QB   (frame_rule) \<longrightarrow> rhoareQB
- Show:  Q{res/x} \<and> QB \<Longrightarrow> B
- Show:  rhoare    C     (callproc x=f(y))   B    (conseq)
- Show:  rhoare    A     (p; callproc x=f(y))   B    (seq with assm)

*)
  define P' where "P' \<equiv> \<lambda>m1 m2. P (memory_update m1 args1 (e_fun y1 m1)) (memory_update m2 args2 (e_fun y2 m2))"
  define x1l where "x1l \<equiv> list_pattern_untyped (p_vars x1)"
  define x2l where "x2l \<equiv> list_pattern_untyped (p_vars x2)"
  define Q' where "Q' \<equiv> \<lambda>m1 m2. (\<exists>res1_val res2_val x1_val x2_val. 
      memory_update_pattern m1 x1 res1_val = m1 \<and> memory_update_pattern m2 x2 res2_val = m2 \<and>
      Q (memory_update (memory_update_untyped_pattern m1 x1l x1_val) res1 res1_val) (memory_update (memory_update_untyped_pattern m2 x2l x2_val) res2 res2_val))"

  define VV1 where "VV1 \<equiv> - {mk_variable_untyped args1}"
  define VV2 where "VV2 \<equiv> UNIV - {mk_variable_untyped args1, mk_variable_untyped res1} - set(p_vars x1)"
  define VV1' where "VV1' \<equiv> - {mk_variable_untyped args2}"
  define VV2' where "VV2' \<equiv> UNIV - {mk_variable_untyped args2, mk_variable_untyped res2} - set(p_vars x2)"

  have y1_VV1: "mk_variable_untyped (args1::'y1 variable) \<notin> VV1" unfolding VV1_def by simp
  have vv1_1: "set (vars_proc_global f1) \<subseteq> VV1" unfolding VV1_def using args1_nin_f1 by auto

  have y2_VV1': "mk_variable_untyped (args2::'y2 variable) \<notin> VV1'" unfolding VV1'_def by simp
  have x1: "set (vars_proc_global f2) \<subseteq> VV1'" unfolding VV1'_def using args2_nin_f2 by auto

  have vv1_2: "VV2 \<subseteq> VV1" unfolding VV2_def VV1_def by auto
  have x1_vv2: "set (p_vars x1) \<inter> VV2 = {}" unfolding VV2_def by auto
  have res_vv2: "set (p_vars (variable_pattern res1 :: 'x1 pattern)) \<inter> VV2 = {}" unfolding VV2_def by auto

  have x2: "VV2' \<subseteq> VV1'" unfolding VV2'_def VV1'_def by auto
  have x3: "set (p_vars (variable_pattern res2 :: 'x2 pattern)) \<inter> VV2' = {}" unfolding VV2'_def by auto
  have x4: "set (p_vars x2) \<inter> VV2' = {}" unfolding VV2'_def by auto

  have foot_Q1: "assertion_footprint_left (insert (mk_variable_untyped (res1::'x1 variable)) VV2 \<union> set(p_vars x1)) Q" 
    apply (rule assertion_footprint_left_mono[OF _ footQ1]) unfolding VV2_def by auto

  have foot_Q2: "assertion_footprint_right (insert (mk_variable_untyped (res2::'x2 variable)) VV2' \<union> set(p_vars x2)) Q"
    apply (rule assertion_footprint_right_mono[OF _ footQ2]) unfolding VV2'_def by auto

  have x1_f1_res_f1: "hoare {\<lambda>m1 m2. (\<forall>v\<in>VV1. memory_lookup_untyped m1 v = memory_lookup_untyped m2 v) \<and> e_fun y1 m1 = e_fun (var_expression args1) m2}
          \<guillemotleft>callproc x1 f1 y1\<guillemotright> ~ \<guillemotleft>callproc (variable_pattern res1) f1 (var_expression args1)\<guillemotright>
        {\<lambda>m1 m2. (\<forall>v\<in>VV2. memory_lookup_untyped m1 v = memory_lookup_untyped m2 v) \<and> memory_pattern_related x1 (variable_pattern res1) m1 m2}"
    apply (rule callproc_equiv)
    using vv1_1 vv1_2 x1_vv2 res_vv2 by auto

  have res_f2_x2_f2: "hoare {\<lambda>m1 m2. (\<forall>v\<in>VV1'. memory_lookup_untyped m1 v = memory_lookup_untyped m2 v) \<and> e_fun (var_expression args2) m1 = e_fun y2 m2}
        \<guillemotleft>callproc (variable_pattern res2) f2 (var_expression args2)\<guillemotright> ~ \<guillemotleft>callproc x2 f2 y2\<guillemotright> 
          {\<lambda>m1 m2. (\<forall>v\<in>VV2'. memory_lookup_untyped m1 v = memory_lookup_untyped m2 v) \<and> memory_pattern_related (variable_pattern res2) x2 m1 m2}"
    apply (rule callproc_equiv)
    using x1 x2 x3 x4 by auto

  have t3: "\<exists>m m'. ((\<forall>v\<in>VV1. memory_lookup_untyped m1 v = memory_lookup_untyped m v) \<and>
                     e_fun y1 m1 = e_fun (var_expression args1) m) \<and>
                    P m m' \<and>
                    (\<forall>v\<in>VV1'. memory_lookup_untyped m' v = memory_lookup_untyped m2 v) \<and> e_fun (var_expression args2) m' = e_fun y2 m2"
                    if "P' m1 m2" for m1 m2
    apply (rule exI[of _ "memory_update m1 args1 (e_fun y1 m1)"], rule exI[of _ "memory_update m2 args2 (e_fun y2 m2)"])
    using y1_VV1 y2_VV1' that unfolding P'_def by simp

  have t4: "Q' m1 m2"
       if eq2: "\<forall>v\<in>VV2'. memory_lookup_untyped m' v = memory_lookup_untyped m2 v" 
       and res_x2: "memory_pattern_related (variable_pattern res2) x2 m' m2" 
       and eq1: "\<forall>v\<in>VV2. memory_lookup_untyped m1 v = memory_lookup_untyped m v" 
       and x1_res: "memory_pattern_related x1 (variable_pattern res1) m1 m"
       and "Q m m'" for m1 m2 m m'
  proof -
    define res1_val where "res1_val \<equiv> memory_lookup m res1 :: 'x1"
    define res2_val where "res2_val \<equiv> memory_lookup m' res2 :: 'x2"
    define x1_val where "x1_val \<equiv> eu_fun (list_expression_untyped (p_vars x1)) m"
    define x2_val where "x2_val \<equiv> eu_fun (list_expression_untyped (p_vars x2)) m'"

    from x1_res
    obtain v where x1_v: "m1 = memory_update_pattern m1 x1 v" and res_v: "m = memory_update_pattern m (variable_pattern res1) v"
      unfolding memory_pattern_related_def by auto
    have "v = res1_val" unfolding res1_val_def apply (subst res_v) by simp
    have x1_res1_val: "memory_update_pattern m1 x1 res1_val = m1" using x1_v `v=res1_val` by simp

    from res_x2
    obtain w where res_w: "m' = memory_update_pattern m' (variable_pattern res2) w" and x2_w: "m2 = memory_update_pattern m2 x2 w"
      unfolding memory_pattern_related_def by auto
    have "w = res2_val" unfolding res2_val_def apply (subst res_w) by simp
    have x2_res2_val: "memory_update_pattern m2 x2 res2_val = m2" using x2_w `w=res2_val` by simp

    have "Q (memory_update (memory_update_untyped_pattern m1 x1l x1_val) res1 res1_val) (memory_update (memory_update_untyped_pattern m2 x2l x2_val) res2 res2_val) = Q m (memory_update (memory_update_untyped_pattern m2 x2l x2_val) res2 res2_val)"
      apply (rule assertion_footprint_leftE[OF foot_Q1])
      using res1_val_def eq1 apply auto
       close (metis list_pattern_untyped_list_expression_untyped lookup_memory_update_untyped_pattern_getter memory_lookup_update_pattern_notsame x1_val_def x1l_def)
      by (metis list_pattern_untyped_list_expression_untyped lookup_memory_update_untyped_pattern_getter pu_vars_list_pattern_untyped x1_val_def x1l_def) 
    also have "\<dots> = Q m m'"
      apply (rule assertion_footprint_rightE[OF foot_Q2])
      using res2_val_def eq2 apply auto
       close (metis list_pattern_untyped_list_expression_untyped lookup_memory_update_untyped_pattern_getter memory_lookup_update_pattern_notsame x2_val_def x2l_def)
      by (metis list_pattern_untyped_list_expression_untyped lookup_memory_update_untyped_pattern_getter pu_vars_list_pattern_untyped x2_val_def x2l_def) 
  finally have Q': "Q (memory_update (memory_update_untyped_pattern m1 x1l x1_val) res1 res1_val)  
                      (memory_update (memory_update_untyped_pattern m2 x2l x2_val) res2 res2_val)"
    using that by simp                      

    from Q' x1_res1_val x2_res2_val show ?thesis unfolding Q'_def by auto
  qed

  have rhoareP'Q': "rhoare P' (callproc x1 f1 y1) (callproc x2 f2 y2) Q'"
    apply (rule rtrans3_rule[OF _ _ x1_f1_res_f1 f1f2 res_f2_x2_f2])
     close (rule t3, simp)
    by (rule t4, simp_all)

  have foot_QB1: "assertion_footprint_left (UNIV - set globals_f1 - set (p_vars x1)) QB"
    unfolding QB_def
    apply (rule assertion_footprint_left_forall)+
    apply (rule assertion_footprint_left_op2[where f="op\<longrightarrow>", OF assertion_footprint_left_const])
    apply (rule assertion_footprint_left_op2[where f="op\<longrightarrow>", OF assertion_footprint_left_const])
    apply (rule assertion_footprint_left_op2[where f="op\<longrightarrow>"])
     apply (rule assertion_footprint_left_update_pattern_untyped[where Y="UNIV - set (p_vars x1)"])
      close (simp, blast)
     apply (rule assertion_footprint_left_update_pattern_untyped[where Y="UNIV"])
      close simp
     apply (rule assertion_footprint_left_update[where Y="UNIV"])
      close
     close (rule assertion_footprint_left_UNIV)
    apply (rule assertion_footprint_left_update_pattern_untyped[where Y="UNIV - set (p_vars x1)"])
     close (simp, blast)
    apply (rule assertion_footprint_left_update_pattern[where Y="UNIV"])
     close simp
    by (rule assertion_footprint_left_UNIV)

  have foot_QB2: "assertion_footprint_right (UNIV - set globals_f2 - set (p_vars x2)) QB"
    unfolding QB_def
    apply (rule assertion_footprint_right_forall)+
    apply (rule assertion_footprint_right_op2[where f="op\<longrightarrow>", OF assertion_footprint_right_const])
    apply (rule assertion_footprint_right_op2[where f="op\<longrightarrow>", OF assertion_footprint_right_const])
    apply (rule assertion_footprint_right_op2[where f="op\<longrightarrow>"])
     apply (rule assertion_footprint_right_update_pattern_untyped[where Y="UNIV - set (p_vars x2)"])
      close (simp, blast)
     apply (rule assertion_footprint_right_update_pattern_untyped[where Y="UNIV"])
      close simp
     apply (rule assertion_footprint_right_update[where Y="UNIV"])
      close
     close (rule assertion_footprint_right_UNIV)
    apply (rule assertion_footprint_right_update_pattern_untyped[where Y="UNIV - set (p_vars x2)"])
     close (simp, blast)
    apply (rule assertion_footprint_right_update_pattern[where Y="UNIV"])
     close simp
    by (rule assertion_footprint_right_UNIV)
    
  have ro_f1: "program_readonly (UNIV - set globals_f1 - set (p_vars x1)) (callproc x1 f1 y1)"
    apply (rule program_readonly_mono[rotated])
     close (rule program_readonly_write_vars)
    using globals_f1 by auto
  have ro_f2: "program_readonly (UNIV - set globals_f2 - set (p_vars x2)) (callproc x2 f2 y2)"
    apply (rule program_readonly_mono[rotated])
     close (rule program_readonly_write_vars)
    using globals_f2 by auto

  have rhoareQB: "hoare {P' &1 &2 \<and> QB &1 &2} \<guillemotleft>callproc x1 f1 y1\<guillemotright> ~ \<guillemotleft>callproc x2 f2 y2\<guillemotright> {Q' &1 &2 \<and> QB &1 &2}"
    apply (rule frame_rule)
        close (fact foot_QB1)
       close (fact foot_QB2)
      close (fact ro_f1)
     close (fact ro_f2)
    by (fact rhoareP'Q')

  have QB_Q: "B m1 m2" if Q'm1m2: "Q' m1 m2" and QBm1m2: "QB m1 m2" for m1 m2
  proof -
    from Q'm1m2 obtain res1_val res2_val x1_val x2_val
      where ux1: "memory_update_pattern m1 x1 res1_val = m1"
        and ux2: "memory_update_pattern m2 x2 res2_val = m2"
        and Q: "Q (memory_update (memory_update_untyped_pattern m1 x1l x1_val) res1 res1_val) 
                  (memory_update (memory_update_untyped_pattern m2 x2l x2_val) res2 res2_val)"
      unfolding Q'_def by auto

    define gL where "gL \<equiv> eu_fun (list_expression_untyped globals_f1) m1"
    define gR where "gR \<equiv> eu_fun (list_expression_untyped globals_f2) m2"
    have gL_type: "gL \<in> t_domain (pu_type (list_pattern_untyped globals_f1))"
      by (metis eu_fun_type gL_def type_list_expression_list_pattern)
    have gR_type: "gR \<in> t_domain (pu_type (list_pattern_untyped globals_f2))"
      by (metis eu_fun_type gR_def type_list_expression_list_pattern)
      

    have Q2: "Q (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f1) gL) x1l x1_val) res1 res1_val)
                (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f2) gR) x2l x2_val) res2 res2_val)"
      unfolding gL_def apply (subst list_pattern_untyped_list_expression_untyped)
      unfolding gR_def apply (subst list_pattern_untyped_list_expression_untyped)
      unfolding ux1 ux2 by (fact Q)

    have B2: "B (memory_update_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f1) gL) x1 res1_val)
                (memory_update_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f2) gR) x2 res2_val)"
      apply (rule QBm1m2[unfolded QB_def, folded x1l_def x2l_def, rule_format, of gL gR x1_val res1_val x2_val res2_val])
        using gL_type gR_type close 2
      unfolding QB_def using Q2 by simp

    show "B m1 m2"
      using B2
      unfolding gL_def apply (subst (asm) list_pattern_untyped_list_expression_untyped)
      unfolding gR_def apply (subst (asm) list_pattern_untyped_list_expression_untyped)
      unfolding ux1 ux2 by simp
  qed

  have rhoareCQ: "hoare {C &1 &2} \<guillemotleft>callproc x1 f1 y1\<guillemotright> ~ \<guillemotleft>callproc x2 f2 y2\<guillemotright> {B &1 &2}"
    apply (rule rconseq_rule[rotated -1])
      close (fact rhoareQB)
     unfolding C_def P'_def close
    using QB_Q by auto

  show ?thesis
    apply (rule rseq_rule)
     close (fact p1p2)
    by (fact rhoareCQ)
qed


lemma callproc_split_args_equiv: 
  assumes fX: "set (vars_proc_global f) \<subseteq> X"
  assumes eX: "set (e_vars e) \<subseteq> X"
  assumes Y: "Y \<subseteq> X \<union> set (p_vars p)"
  assumes xX: "mk_variable_untyped x \<notin> X"
  shows "obs_eq X Y (callproc p f e) (seq (assign (variable_pattern x) e) (callproc p f (var_expression x)))"
proof -
  define Y' where "Y' \<equiv> Y - set (p_vars p)"

  have callproc_eq: "hoare {(\<forall>x\<in>X. memory_lookup_untyped &1 x = memory_lookup_untyped &2 x) \<and> e_fun e &1 = e_fun (var_expression x) &2}
    \<guillemotleft>callproc p f e\<guillemotright> ~ \<guillemotleft>callproc p f (var_expression x)\<guillemotright> {(\<forall>v\<in>Y'. memory_lookup_untyped &1 v = memory_lookup_untyped &2 v)
                      \<and> memory_pattern_related p p &1 &2}"
    apply (rule callproc_equiv) close (rule fX)
    using Y'_def Y by auto

  hence rh_call: "hoare {(\<forall>x\<in>X. memory_lookup_untyped &1 x = memory_lookup_untyped &2 x) \<and> e_fun e &1 = e_fun (var_expression x) &2}
    \<guillemotleft>callproc p f e\<guillemotright> ~ \<guillemotleft>callproc p f (var_expression x)\<guillemotright> {(\<forall>v\<in>Y. memory_lookup_untyped &1 v = memory_lookup_untyped &2 v)}"
    apply (rule rconseq_rule[rotated -1]) 
     close auto
    unfolding Y'_def
    by (metis DiffI lookup_memory_update_untyped_pattern_getter memory_pattern_related_def memory_update_pattern_def p_vars_def)

  have impl1: "memory_lookup_untyped m y = memory_lookup_untyped (memory_update_pattern m' (variable_pattern x) (e_fun e m')) y"
           if "y\<in>X" and Y'_eq: "\<And>v. v\<in>X \<Longrightarrow> memory_lookup_untyped m v = memory_lookup_untyped m' v"
           for m m' y
    using xX that by auto

  have impl2: "(e_fun e m = e_fun (var_expression x) (memory_update_pattern m' (variable_pattern x) (e_fun e m')))"
           if Y'_eq: "\<And>v. v\<in>X \<Longrightarrow> memory_lookup_untyped m v = memory_lookup_untyped m' v"
           for m m'
    using eX apply auto
    by (meson e_fun_footprint subsetCE that)

  have "obs_eq X Y (seq Lang_Typed.skip (callproc p f e)) (seq (assign (variable_pattern x) e) (callproc p f (var_expression x)))"
    unfolding obs_eq_def
    apply (rule rseq_rule[rotated])
     close (fact rh_call) 
    apply (rule assign_right_rule)
    using impl1 impl2 by metis

  thus "obs_eq X Y (callproc p f e) (seq (assign (variable_pattern x) e) (callproc p f (var_expression x)))"
    unfolding obs_eq_def by (simp add: rhoare_def)
qed

lemma callproc_split_result_equiv: 
  assumes fX: "set (vars_proc_global f) \<subseteq> X"
  assumes eX: "set (e_vars e) \<subseteq> X"
  assumes Y: "Y \<subseteq> X \<union> set (p_vars p)"
  assumes xY: "mk_variable_untyped x \<notin> Y"
  shows "obs_eq X Y (callproc p f e) (seq (callproc (variable_pattern x) f e) (assign p (var_expression x)))"
proof -
  define Y' where "Y' \<equiv> Y - set (p_vars p)"
  have callproc_eq: "hoare {(\<forall>x\<in>X. memory_lookup_untyped &1 x = memory_lookup_untyped &2 x) \<and> e_fun e &1 = e_fun e &2}
    \<guillemotleft>callproc p f e\<guillemotright> ~ \<guillemotleft>callproc (variable_pattern x) f e\<guillemotright> {(\<forall>v\<in>Y'. memory_lookup_untyped &1 v = memory_lookup_untyped &2 v)
                      \<and> memory_pattern_related p (variable_pattern x) &1 &2}"
    apply (rule callproc_equiv) close (rule fX)
      using Y'_def Y xY by auto
  hence rh_call: "hoare {(\<forall>x\<in>X. memory_lookup_untyped &1 x = memory_lookup_untyped &2 x)}
    \<guillemotleft>callproc p f e\<guillemotright> ~ \<guillemotleft>callproc (variable_pattern x) f e\<guillemotright> {(\<forall>v\<in>Y'. memory_lookup_untyped &1 v = memory_lookup_untyped &2 v)
                      \<and> memory_pattern_related p (variable_pattern x) &1 &2}"
    apply (rule rconseq_rule[rotated -1]) 
     using eX e_fun_footprint close blast
    by simp
  have impl: "memory_lookup_untyped m y = memory_lookup_untyped (memory_update_pattern m' p (e_fun (var_expression x) m')) y"
            if "y\<in>Y" and Y'_eq: "\<And>v. v\<in>Y' \<Longrightarrow> memory_lookup_untyped m v = memory_lookup_untyped m' v" and p_rel: "memory_pattern_related p (variable_pattern x) m m'"
           for m m' y
  proof (cases "y\<in>set(p_vars p)")
    case True
      thus ?thesis using p_rel
      by (metis e_fun_var_expression lookup_memory_update_untyped_pattern_getter memory_lookup_update_same memory_pattern_related_def memory_update_pattern_def memory_update_variable_pattern p_vars_def)
    next case False
      thus ?thesis using `y\<in>Y` Y'_eq unfolding Y'_def 
      by (simp add: DiffI memory_lookup_update_pattern_notsame memory_update_pattern_def p_vars_def)
  qed
  have "obs_eq X Y (seq (callproc p f e) Lang_Typed.skip) (seq (callproc (variable_pattern x) f e) (assign p (var_expression x)))"
    unfolding obs_eq_def
    apply (rule rseq_rule)
     close (fact rh_call) 
    apply (rule assign_right_rule)
    using impl by auto
  thus "obs_eq X Y (callproc p f e) (seq (callproc (variable_pattern x) f e) (assign p (var_expression x)))"
    unfolding obs_eq_def by (simp add: rhoare_def)     
qed


end
