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
using assms unfolding e_fun_eu_fun rhoare_untyped by auto

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
  def body' \<equiv> "Rep_program (p_body p)"
  def pargs' \<equiv> "Rep_pattern (p_arg p)"
  def ret' \<equiv> "mk_expression_untyped (p_return p)"
  def p' \<equiv>  "Proc body' pargs' ret'"
  have p': "mk_procedure_untyped p = p'"
    unfolding mk_procedure_untyped_def p'_def body'_def pargs'_def ret'_def ..
  def x' \<equiv> "Rep_pattern x"
  def args' \<equiv> "mk_expression_untyped args"
  have callproc: "Rep_program (callproc x p args) == CallProc x' p' args'"
    unfolding Rep_callproc x'_def[symmetric] p' args'_def[symmetric] by assumption
  def unfolded' \<equiv> "Seq (Seq (Seq (Assign pargs' args') (assign_default non_parg_locals)) body')
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
  def body' == "p_body (rename_local_variables_proc renaming p)"
  def ret' == "p_return (rename_local_variables_proc renaming p)"
  def pargs' == "p_arg (rename_local_variables_proc renaming p)"
  def unfolded' == "seq (seq (seq (assign pargs' args) (assign_default_typed non_parg_locals)) body') (assign x ret')"
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
definition "assertion_footprint X P == (\<forall>m1 m2. (\<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) \<longrightarrow> P m1 = P m2)"
lemma assertion_footprint_const: "assertion_footprint X (\<lambda>m. P)"
  unfolding assertion_footprint_def by simp
lemma assertion_footprint_lookup: "mk_variable_untyped x \<in> X \<Longrightarrow> assertion_footprint X (\<lambda>m. memory_lookup m x)"
  unfolding assertion_footprint_def by auto
lemma assertion_footprint_app: "assertion_footprint X P \<Longrightarrow> assertion_footprint X Q \<Longrightarrow> assertion_footprint X (\<lambda>m. (P m) (Q m))"
  unfolding assertion_footprint_def by auto

definition "assertion_footprint_left X P == (\<forall>m1 m1' m2 m2'. (\<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m1' x) \<longrightarrow> (m2::memory)=m2' \<longrightarrow> P m1 m2 = P m1' m2')"
lemma assertion_footprint_left_const: "assertion_footprint_left X (\<lambda>m. P)"
  unfolding assertion_footprint_left_def by simp
lemma assertion_footprint_left_lookup: "mk_variable_untyped x \<in> X \<Longrightarrow> assertion_footprint_left X (\<lambda>m1 m2. memory_lookup m1 x)"
  unfolding assertion_footprint_left_def by auto
lemma assertion_footprint_left_app: "assertion_footprint_left X P \<Longrightarrow> assertion_footprint_left X Q \<Longrightarrow> assertion_footprint_left X (\<lambda>m m'. (P m m') (Q m m'))"
  unfolding assertion_footprint_left_def by auto

definition "assertion_footprint_right X P == (\<forall>m1 m1' m2 m2'. (\<forall>x\<in>X. memory_lookup_untyped m2 x = memory_lookup_untyped m2' x)\<longrightarrow> (m1::memory)=m1' \<longrightarrow> P m1 m2 = P m1' m2')"
lemma assertion_footprint_right_const: "assertion_footprint_right X (\<lambda>m m'. P m)"
  unfolding assertion_footprint_right_def by simp
lemma assertion_footprint_right_lookup: "mk_variable_untyped x \<in> X \<Longrightarrow> assertion_footprint_right X (\<lambda>m1 m2. memory_lookup m2 x)"
  unfolding assertion_footprint_right_def by auto
lemma assertion_footprint_right_app: "assertion_footprint_right X P \<Longrightarrow> assertion_footprint_right X Q \<Longrightarrow> assertion_footprint_right X (\<lambda>m m'. (P m m') (Q m m'))"
  unfolding assertion_footprint_right_def by auto

lemma rskip_rule [simp]:
  assumes "\<forall>m m'. P m m' \<longrightarrow> Q m m'"
  shows "hoare {P &1 &2} skip ~ skip {Q &1 &2}"
  using assms by (simp add: rhoare_untyped RHL_Untyped.rskip_rule)

lemma rskip_rule_strict: "hoare {P &1 &2} skip ~ skip {P &1 &2}"
  by (simp add: rhoare_untyped RHL_Untyped.rskip_rule)

lemma obseq_context_as_rule:
  fixes X defines "eq == \<lambda>(m1\<Colon>memory) m2\<Colon>memory. \<forall>x\<Colon>variable_untyped\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  assumes obseq: "obseq_context X C"
  assumes rh: "rhoare eq c d eq"
  shows "rhoare eq (C c) (C d) eq"
using assms unfolding obseq_context_def obs_eq_def eq_def by auto

lemma obseq_context_seq:                                        
  assumes "obseq_context X C1"
  assumes "obseq_context X C2"
  shows "obseq_context X (\<lambda>c. seq (C1 c) (C2 c))"
proof -
  def eq == "\<lambda>(m1\<Colon>memory) m2\<Colon>memory. \<forall>x\<Colon>variable_untyped\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
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

(* TODO move *)
lemma e_fun_footprint: 
  assumes "\<And>v. v\<in>set (e_vars e) \<Longrightarrow> memory_lookup_untyped m1 v = memory_lookup_untyped m2 v"
  shows "e_fun (e::'a::prog_type expression) m1 = e_fun e m2"
unfolding e_fun_eu_fun o_def
apply (tactic \<open>cong_tac @{context} 1\<close>, simp)
apply (subst eu_fun_footprint)
using assms unfolding e_vars_eu_vars by auto

lemma obseq_context_ifte: 
  assumes C1: "obseq_context X C1"
  assumes C2: "obseq_context X C2"
  assumes vars: "set (e_vars e) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. ifte e (C1 c) (C2 c))"
proof -
  def eq == "\<lambda>(m1\<Colon>memory) m2\<Colon>memory. \<forall>x\<Colon>variable_untyped\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
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
  assumes "obseq_context X C1"
  assumes "set (e_vars e) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. Lang_Typed.while e (C1 c))"
SORRY

lemma obseq_context_empty: 
  shows "obseq_context X (\<lambda>c. c)"
unfolding obseq_context_def by simp


lemma obseq_context_assign: 
  assumes "set (p_vars x) \<subseteq> X"
  assumes "set (e_vars e) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. assign x e)"
SORRY

lemma obseq_context_skip: "obseq_context X (\<lambda>c. Lang_Typed.skip)"
  unfolding obseq_context_def apply auto unfolding obs_eq_def
  by (simp add: rhoare_untyped RHL_Untyped.rskip_rule)

lemma obseq_context_sample: 
  assumes "set (p_vars x) \<subseteq> X"
  assumes "set (e_vars e) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. sample x e)"
SORRY

lemma obseq_context_callproc_allglobals: 
  fixes X' defines "X==X' \<union> Collect vu_global"
  assumes "set (p_vars x) \<subseteq> X"
  assumes "set (e_vars a) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. callproc x p a)"
SORRY

  

lemma hoare_obseq_replace: 
  assumes "obseq_context X C"
  assumes "assertion_footprint X Q"
  assumes "obs_eq' X c d"
  assumes "hoare {P &m} \<guillemotleft>C d\<guillemotright> {Q &m}"
  shows "hoare {P &m} \<guillemotleft>C c\<guillemotright> {Q &m}"
SORRY "check assumptions carefully!"

lemma rhoare_left_obseq_replace: 
  assumes "obseq_context X C"
  assumes "assertion_footprint_left X Q"
  assumes "obs_eq' X c d"
  assumes "hoare {P &1 &2} \<guillemotleft>C d\<guillemotright> ~ \<guillemotleft>c'\<guillemotright> {Q &1 &2}"
  shows "hoare {P &1 &2} \<guillemotleft>C c\<guillemotright> ~ \<guillemotleft>c'\<guillemotright> {Q &1 &2}"
by (smt assertion_footprint_left_def assms obs_eq'_def obs_eq_def obseq_context_def rhoare_untyped rtrans_rule)

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


end
