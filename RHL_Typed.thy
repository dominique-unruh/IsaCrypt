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

lemma rhoare_untyped: "rhoare P c1 c2 Q = rhoare_untyped P (mk_program_untyped c1) (mk_program_untyped c2) Q"
  unfolding rhoare_def rhoare_untyped_def denotation_def ..


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
                      (const_expression_untyped (vu_type v) (t_default (vu_type v))))) (mk_program_untyped p0) vs)"

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
  defines "pargs == p_args p"
  defines "GL == {x. vu_global x}"
  assumes proc_locals: "(set(local_vars body) \<union> set(p_vars pargs) \<union> set(e_vars ret)) - GL \<subseteq> set locals"
  assumes locals_local: "GL \<inter> set locals = {}"
  assumes localsV: "V \<inter> set locals \<subseteq> set (p_vars x)"
  assumes proc_globals: "(set(vars body) \<union> set(e_vars ret)) \<inter> GL \<subseteq> V"
  assumes argvarsV: "set(e_vars args) \<subseteq> V"
  assumes non_parg_locals: "set non_parg_locals = set locals - set (p_vars pargs)"

  defines "unfolded == seq (seq (seq (assign pargs args) (assign_default_typed non_parg_locals)) body) (assign x ret)"
  shows "obs_eq' V (callproc x p args) unfolded"
proof -
(*  have body_local_old: "\<And>x. x \<in> set (vars body) \<Longrightarrow> \<not> vu_global x \<Longrightarrow> x \<in> set locals" 
    using body_local unfolding local_vars_def by auto*)

  def body' \<equiv> "mk_program_untyped (p_body p)"
  def pargs' \<equiv> "mk_pattern_untyped (p_args p)"
  def ret' \<equiv> "mk_expression_untyped (p_return p)"
  def p' \<equiv>  "Proc body' pargs' ret'"
  have p': "mk_procedure_untyped p = p'"
    unfolding mk_procedure_untyped_def p'_def body'_def pargs'_def ret'_def ..
  def x' \<equiv> "mk_pattern_untyped x"
  def args' \<equiv> "mk_expression_untyped args"
  have callproc: "mk_program_untyped (callproc x p args) == CallProc x' p' args'"
    unfolding mk_untyped_callproc x'_def[symmetric] p' args'_def[symmetric] .
  def unfolded' \<equiv> "Seq (Seq (Seq (Assign pargs' args') (assign_default non_parg_locals)) body')
                           (Assign x' ret')"
(* Seq (Seq (assign_local_vars locals pargs' args') body') (Assign (pattern_1var x') ret')" *)
  have assign: "mk_program_untyped (assign_default_typed locals) == assign_default locals"
      unfolding assign_default_typed_def 
      apply (subst Abs_program_inverse, auto)
      by (rule assign_default_welltyped)
  have unfolded: "Rep_program unfolded = unfolded'"
    unfolding unfolded'_def unfolded_def program_def pargs'_def pargs_def args'_def
    mk_untyped_seq assign body'_def body_def mk_untyped_assign ret_def
    x'_def[symmetric] ret'_def[symmetric] assign_default_typed_def
   apply (subst Abs_program_inverse)
   using assign_default_welltyped by auto
  show "obs_eq' V (callproc x p args) unfolded"
    unfolding obs_eq'_def obs_eq_obs_eq_untyped callproc unfolded unfolded'_def p'_def 
    apply (rule callproc_rule) 
    unfolding body'_def x'_def vars_def[symmetric] e_vars_def[symmetric] p_vars_def[symmetric] pargs'_def ret'_def args'_def 
    using assms local_vars_def by auto
qed

(* Outputs the list of parameters of callproc_rule, ordered like the arguments to Drule.instantiate' *)
ML {* Term.add_vars (Thm.prop_of @{thm callproc_rule}) [] |> rev |> map Var |> map (Syntax.string_of_term @{context}) |> String.concatWith "\n" |> writeln *}

print_theorems

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

lemma obseq_context_seq: 
  assumes "obseq_context X C1"
  assumes "obseq_context X C2"
  shows "obseq_context X (\<lambda>c. seq (C1 c) (C2 c))"
SORRY

lemma obseq_context_ifte: 
  assumes "obseq_context X C1"
  assumes "obseq_context X C2"
  assumes "set (e_vars e) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. ifte e (C1 c) (C2 c))"
SORRY

lemma obseq_context_while: 
  assumes "obseq_context X C1"
  assumes "set (e_vars e) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. Lang_Typed.while e (C1 c))"
SORRY

lemma obseq_context_empty: 
  shows "obseq_context X (\<lambda>c. c)"
SORRY


lemma obseq_context_assign: 
  assumes "set (p_vars x) \<subseteq> X"
  assumes "set (e_vars e) \<subseteq> X"
  shows "obseq_context X (\<lambda>c. assign x e)"
SORRY

lemma obseq_context_skip: "obseq_context X (\<lambda>c. Lang_Typed.skip)"
  unfolding obseq_context_def apply auto unfolding obs_eq_def
  by (simp add: rhoare_untyped rskip_rule)

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




end
