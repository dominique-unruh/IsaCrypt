theory RHL_Typed
imports RHL_Untyped Hoare_Typed
begin

subsection {* Definition *}

definition rhoare :: "(memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> program \<Rightarrow> (memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "rhoare pre c1 c2 post =
  (\<forall>m1 m2. pre m1 m2 \<longrightarrow> 
     (\<exists>\<mu>. apply_to_distr fst \<mu> = denotation c1 m1
        \<and> apply_to_distr snd \<mu> = denotation c2 m2
        \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> post m1' m2')))"

lemma rhoare_untyped: "rhoare P c1 c2 Q = rhoare_untyped P (mk_program_untyped c1) (mk_program_untyped c2) Q"
  unfolding rhoare_def rhoare_untyped_def denotation_def ..


definition "obs_eq X Y c1 c2 ==
  rhoare (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)
         c1 c2
         (\<lambda>m1 m2. \<forall>x\<in>Y. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"

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


(* TODO move *)
lemma vars_seq [simp]: "vars (seq a b) = vars a @ vars b" SORRY
lemma vars_assign [simp]: "vars (assign x e) = mk_variable_untyped x # e_vars e" SORRY
lemma procargvars_add_untyped [simp]: "mk_procargvars_untyped (procargvars_add x a) = mk_variable_untyped x # mk_procargvars_untyped a" SORRY
lemma procargvars_empty_untyped [simp]: "mk_procargvars_untyped procargvars_empty = []" SORRY
lemma procargs_add_untyped [simp]: "mk_procargs_untyped (procargs_add x a) = mk_expression_untyped x # mk_procargs_untyped a" SORRY
lemma procargs_empty_untyped [simp]: "mk_procargs_untyped procargs_empty = []" SORRY
lemma LVariable_local [simp]: "\<not> vu_global (mk_variable_untyped (LVariable x))"
  by (simp add: mk_variable_untyped_def)
lemma vars_procargs_add [simp]: "vars_procargs (procargs_add e a) = e_vars e @ vars_procargs a" SORRY
lemma vars_procargs_empty [simp]: "vars_procargs procargs_empty = []" SORRY
lemma mk_variable_untyped_distinct [simp]: "a \<noteq> b \<Longrightarrow> mk_variable_untyped (LVariable a) \<noteq> mk_variable_untyped (LVariable b)"
  by (simp add: mk_variable_untyped_def)


definition "assign_local_vars_typed locals (pargs::'a::procargs procargvars) (args::'a procargs)
  = Abs_program (assign_local_vars locals (mk_procargvars_untyped pargs) (mk_procargs_untyped args))"

lemma assign_local_vars_typed_simp1 [simp]: 
  "assign_local_vars_typed locals (procargvars_add p pargs) (procargs_add e args) = 
   seq (assign_local_vars_typed locals pargs args) (assign p e)"
unfolding assign_local_vars_typed_def seq_def assign_def apply simp
apply (subst Abs_program_inverse, auto intro!: well_typed_assign_local_vars)
by (subst Abs_program_inverse, auto)

(* TODO move *)
lemma t_default_Type [simp]: "t_default (Type TYPE('a::prog_type)) = embedding (default::'a)"
  by (simp add: Abs_type_inverse t_default_def Type_def)

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

(* If the number of subgoals change, inline_rule_conditions_tac must be adapted accordingly *)
lemma inline_rule:
  fixes p::"('a::procargs,'b::prog_type) procedure" and x::"'b variable" and args::"'a procargs"
    and locals::"variable_untyped list"
  defines "body == p_body p"
  defines "ret == p_return p"
  defines "pargs == p_args p"
  assumes body_local: "\<And>x. x \<in> set (vars body) \<Longrightarrow> \<not> vu_global x \<Longrightarrow> x \<in> set locals"
  assumes pargs_local: "set (mk_procargvars_untyped pargs) \<subseteq> set locals"
  assumes ret_local: "set (e_vars ret) \<subseteq> set locals"
  assumes locals_local: "\<And>x. x\<in>set locals \<Longrightarrow> \<not>vu_global x"
  assumes argvars_locals: "\<And>x. x\<in>set(vars_procargs args) \<Longrightarrow> x\<notin>set locals"
  assumes localsV: "V \<inter> set locals \<subseteq> {mk_variable_untyped x}"
  assumes globalsVbody: "\<And>x. x\<in>set(vars body) \<Longrightarrow> vu_global x \<Longrightarrow> x\<in>V"
  assumes globalsVret: "\<And>x. x\<in>set(e_vars ret) \<Longrightarrow> vu_global x \<Longrightarrow> x\<in>V"
  assumes argvarsV: "set(vars_procargs args) \<subseteq> V"
  defines "unfolded == seq (seq (assign_local_vars_typed locals pargs args) body) (assign x ret)"
  shows "obs_eq V V (callproc x p args) unfolded"
proof -
  def body' \<equiv> "mk_program_untyped (p_body p)"
  def pargs' \<equiv> "mk_procargvars_untyped (p_args p)"
  def ret' \<equiv> "mk_expression_untyped (p_return p)"
  def p' \<equiv>  "Proc body' pargs' ret'"
  have p': "mk_procedure_untyped p = p'"
    unfolding mk_procedure_untyped_def p'_def body'_def pargs'_def ret'_def ..
  def x' \<equiv> "mk_variable_untyped x"
  def args' \<equiv> "mk_procargs_untyped args"
  have callproc: "mk_program_untyped (callproc x p args) == CallProc x' p' args'"
    unfolding mk_untyped_callproc x'_def[symmetric] p' args'_def[symmetric] .
  def unfolded' \<equiv> "Seq (Seq (assign_local_vars locals pargs' args') body') (Assign x' ret')"
  have assign: "mk_program_untyped (assign_local_vars_typed locals pargs args)
      == assign_local_vars locals pargs' args'"
      unfolding assign_local_vars_typed_def pargs'_def args'_def pargs_def 
      apply (subst Abs_program_inverse, auto)
      apply (rule well_typed_assign_local_vars)
      by simp
  have unfolded: "Rep_program unfolded = unfolded'"
    unfolding unfolded'_def unfolded_def program_def
    mk_untyped_seq assign body'_def body_def mk_untyped_assign ret_def
    x'_def[symmetric] ret'_def[symmetric] ..
  show "obs_eq V V (callproc x p args) unfolded"
    unfolding obs_eq_obs_eq_untyped callproc unfolded unfolded'_def p'_def 
    apply (rule inline_rule)
    unfolding body'_def vars_def[symmetric] pargs'_def ret'_def args'_def
    using body_local body_def close auto
    using pargs_local pargs_def close auto
    using ret_local ret_def close auto
    using locals_local close auto
    using argvars_locals unfolding vars_procargs_def close auto
    using localsV x'_def  close auto
    using globalsVbody body_def close auto
    using globalsVret ret_def close auto
    using argvarsV unfolding vars_procargs_def by auto
qed

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
definition "local_assertion X P == (\<forall>m1 m2. (\<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) \<longrightarrow> P m1 = P m2)"

lemma obseq_context_seq: 
  assumes "obseq_context X C1"
  assumes "obseq_context X C2"
  shows "obseq_context X (\<lambda>c. seq (C1 c) (C2 c))"
SORRY

lemma obseq_context_empty: 
  shows "obseq_context X (\<lambda>c. c)"
SORRY


lemma obseq_context_assign: 
  assumes "mk_variable_untyped x \<in> X"
  assumes "set (e_vars e) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. assign x e)"
SORRY

lemma hoare_obseq_replace: 
  assumes "obseq_context X C"
  assumes "local_assertion X Q"
  assumes "obs_eq X X c d"
  assumes "hoare {P &m} \<guillemotleft>C d\<guillemotright> {Q &m}"
  shows "hoare {P &m} \<guillemotleft>C c\<guillemotright> {Q &m}"
SORRY "check assumptions carefully!"




end
