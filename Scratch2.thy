theory Scratch2
imports RHL_Typed Hoare_Tactics Procs_Typed Tactic_Inline
begin

(*definition "HIDDEN_EQ = op="*)
lemma HIDDEN_EQ_refl: "HIDDEN_EQ x x" unfolding HIDDEN_EQ_def ..
lemma HIDDEN_EQ_procargs:
  shows "HIDDEN_EQ procargvars_empty procargvars_empty"
    and "HIDDEN_EQ a b \<Longrightarrow> HIDDEN_EQ (procargvars_add (LVariable x) a) (procargvars_add (LVariable x) b)"
unfolding HIDDEN_EQ_def by auto
lemma HIDDEN_EQ_varset:
  fixes x x' y y'
  defines "x == mk_variable_untyped (LVariable x')"
  defines "y == mk_variable_untyped (Variable y')"
  shows "HIDDEN_EQ {} {}"
    and "HIDDEN_EQ a b \<Longrightarrow> HIDDEN_EQ (Set.insert x a) (Set.insert x b)"
    and "HIDDEN_EQ a b \<Longrightarrow> HIDDEN_EQ (Set.insert y a) (Set.insert y b)"
    and "HIDDEN_EQ a b \<Longrightarrow> HIDDEN_EQ a' b' \<Longrightarrow> HIDDEN_EQ (a \<union> a') (b \<union> b')"
unfolding HIDDEN_EQ_def by auto
lemma HIDDEN_EQ_I': "HIDDEN_EQ a b \<Longrightarrow> a==b" by (simp add: HIDDEN_EQ_def)
lemma HIDDEN_EQ_D': "a==b \<Longrightarrow> HIDDEN_EQ a b" by (simp add: HIDDEN_EQ_def)

lemma vars_proc_global_inter_vu_global: 
  "set (vars_proc_global f) \<inter> Collect vu_global = set (vars_proc_global f)"
unfolding vars_proc_global_def by auto

abbreviation "globVar == Variable ''globVar''"


lemma filter_locals1: "Set.filter (\<lambda>x. \<not> vu_global x) (insert (mk_variable_untyped (LVariable x :: 'a::prog_type variable)) V)
  = insert (mk_variable_untyped (LVariable x :: 'a variable)) (Set.filter (\<lambda>x. \<not> vu_global x) V)"
  by auto
lemma filter_locals2: "Set.filter (\<lambda>x. \<not> vu_global x) (insert (mk_variable_untyped (Variable x :: 'a::prog_type variable)) V)
  = Set.filter (\<lambda>x. \<not> vu_global x) V"
  by auto
lemma filter_locals3: "Set.filter (\<lambda>x. \<not> vu_global x) (set (vars_proc_global f)) = {}"
  using vars_proc_global_inter_vu_global by fastforce 

definition_by_specification testproc :: "(unit,unit) procedure \<Rightarrow> (int*unit,int)procedure" where
  "testproc f = LOCAL x y a z. proc(a) {x:=a; z:=call f(); y:=(1::int); globVar:=x; return x+y;}"
schematic_lemma testproc_body [procedure_info]: "p_body (testproc f) == ?b" unfolding testproc_def by simp
schematic_lemma testproc_return [procedure_info]: "p_return (testproc f) == ?b" unfolding testproc_def by simp
schematic_lemma testproc_args [procedure_info]: "p_args (testproc f) == ?b" unfolding testproc_def by simp
schematic_lemma testproc_body_vars [procedure_info]: "set (vars_proc_global f) == fv \<Longrightarrow> set (vars (p_body (testproc f))) == ?b" unfolding testproc_body by simp
schematic_lemma testproc_body_local_vars [procedure_info]: "set (local_vars (p_body (testproc f))) == ?b" 
 apply (rule HIDDEN_EQ_I')
 unfolding local_vars_def filter_set[symmetric] apply (subst testproc_body_vars) apply simp_all
 unfolding filter_locals1 filter_locals2 filter_locals3
 by (rule HIDDEN_EQ_varset)+
schematic_lemma testproc_body_vars': "set (vars (p_body (testproc f))) == ?b" by (subst testproc_body_vars, simp, simp)
schematic_lemma testproc_global_vars [procedure_info]: assumes "set (vars_proc_global f) == fv" shows "set (vars_proc_global (testproc f)) == ?b" 
 apply (rule HIDDEN_EQ_I')
 unfolding vars_proc_global_def testproc_body testproc_return 
 apply (simp add: vars_proc_global_inter_vu_global)
 unfolding assms
 by (rule HIDDEN_EQ_varset HIDDEN_EQ_refl[of fv])+
schematic_lemma testproc_global_vars': "set (vars_proc_global (testproc f)) == ?b" by (subst testproc_global_vars, simp, simp)
schematic_lemma testproc_return_vars [procedure_info]: "set (e_vars (p_return (testproc f))) == ?b" unfolding testproc_return by simp


ML {*
(*
fun procedure_get_info_tac ctx localfacts =
  let val facts = Proof_Context.get_fact ctx (Facts.named "procedure_info")
      val simpset = put_simpset HOL_basic_ss ctx addsimps facts addsimps localfacts
  in
  rtac @{thm HIDDEN_EQ_I'} 1
  THEN
  simp_tac simpset 1
  THEN
  rtac @{thm HIDDEN_EQ_refl} 1
  end
*)


*}

schematic_lemma 
shows "set (vars (p_body (testproc f))) = ?xxx"
by (tactic {* Tactic_Inline.procedure_get_info_tac @{context} @{thms assms} true *})



ML {*
(*fun procedure_get_info suffix ctx proc =
  case proc of 
    Const(procname,_) => Proof_Context.get_thm ctx (procname^suffix) |> Local_Defs.meta_rewrite_rule ctx
  | _ => (@{print} proc; raise TERM("procedure_get_info expects a constant",[proc]))

val procedure_get_args = procedure_get_info "_args";
val procedure_get_body = procedure_get_info "_body";
val procedure_get_return = procedure_get_info "_return";
val procedure_get_body_vars = procedure_get_info "_body_vars";
val procedure_get_return_vars = procedure_get_info "_return_vars";
*)


*}

ML {*
*}
ML {*
*}


ML {*
*}

ML {*
*}



ML {*
*}


schematic_lemma 
shows "set (vars (p_body (testproc f))) == ?xxx"
by (tactic {* Tactic_Inline.procedure_get_info_tac @{context} [] true *})

lemma 
  assumes "\<And>c'::int. LOCAL x z. hoare {$x=c'} z:=call f() {$x=c'}"
  shows  "\<And>z. LOCAL b c x. hoare {b=3} b:=$b+2; c:=call testproc f(b+z) {c=6+z}"
ML_prf {* Tactic_Inline.procedure_get_info @{context} [] true @{term "set (vars (p_body (testproc f)))"} *}
ML_prf {* Tactic_Inline.procedure_get_thms  @{context} [] true @{term "testproc f"} *}
apply (tactic {* Tactic_Inline.inline_tac @{context} [] @{term "testproc f"} 1 *})
apply simp apply wp
apply (seq 2) defer
apply (seq 1) defer
close (simp, fact assms) defer
apply (wp, skip, auto)
by (wp, skip, auto)


(*
apply (tactic {*
let val callproc = callproc_rule_tac @{context}
    val obseq = hoare_obseq_replace_tac @{context} (Proof_Context.read_term_pattern @{context} "callproc _ _ _") callproc 1
in
obseq
end
*})
*)


(*apply (tactic \<open>hoare_obseq_replace_tac @{context} (Proof_Context.read_term_pattern @{context} "callproc _ _ _") (K (K all_tac)) 1\<close>)*)
(*apply (rule hoare_obseq_replace[where c="callproc _ _ _" and 
  X="{mk_variable_untyped (LVariable ''b''::int variable), mk_variable_untyped (LVariable ''c''::int variable)} \<union> Collect vu_global"])
  close (auto intro!: obseq_context_empty obseq_context_seq obseq_context_assign obseq_context_sample  obseq_context_ifte obseq_context_while obseq_context_callproc_allglobals) -- "Show that context allows X-rewriting"
  close (unfold assertion_footprint_def memory_lookup_def, fastforce) -- "Show that the postcondition is X-local"   *)


end
