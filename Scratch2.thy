theory Scratch2
imports RHL_Typed Hoare_Tactics Procs_Typed Tactic_Inline 
begin

definition "HIDDEN_EQ = op="
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

procedure testproc :: "(unit,unit) procedure \<Rightarrow> (int*unit,int)procedure" where
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



section "MODULE TYPE"

type_synonym 'a testmodule_rep = "(('a*unit,unit)procedure * (unit,'a) procedure)"

typedef 'a testmodule = "UNIV::'a testmodule_rep set" by auto

instantiation testmodule :: (prog_type)procedure_functor begin
definition "procedure_functor_type (_::'a testmodule itself) == procedure_functor_type (TYPE('a testmodule_rep))"
definition "procedure_functor_mk_untyped x == procedure_functor_mk_untyped (Rep_testmodule x)"
definition "procedure_functor_mk_typed' p == Abs_testmodule (procedure_functor_mk_typed' p)"
instance 
  apply intro_classes
  close (unfold procedure_functor_mk_untyped_testmodule_def procedure_functor_type_testmodule_def, fact procedure_functor_welltyped)
  close (unfold procedure_functor_mk_untyped_testmodule_def, fact procedure_functor_beta_reduced)
  close (unfold procedure_functor_mk_untyped_testmodule_def procedure_functor_mk_typed'_testmodule_def procedure_functor_type_testmodule_def Abs_testmodule_inverse[OF Set.UNIV_I],
         fact procedure_functor_mk_typed_inverse')
  apply (unfold procedure_functor_mk_typed'_testmodule_def procedure_functor_mk_untyped_testmodule_def Rep_testmodule_inverse procedure_functor_mk_untyped_inverse')
  by (fact refl)
end

term testmodule

definition "proc1 module = (case module of (proc1_,proc2_) \<Rightarrow> proc1_)"
definition "proc2 module = (case module of (proc1_,proc2_) \<Rightarrow> proc2_)"
definition "testmodule x_proc1 x_proc2 == Abs_testmodule (x_proc1,x_proc2)"

term "x::int testmodule == y::_::procedure_functor"




end
