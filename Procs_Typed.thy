theory Procs_Typed
imports Lang_Typed Procedures
begin

subsection {* Procedure functors *}

class procedure_functor =
  fixes procedure_functor_type :: "'a itself \<Rightarrow> procedure_type_open"
  fixes procedure_functor_mk_untyped :: "'a \<Rightarrow> procedure_rep"
  fixes procedure_functor_mk_typed' :: "procedure_rep \<Rightarrow> 'a"
  assumes procedure_functor_welltyped: "well_typed_proc'' [] (procedure_functor_mk_untyped (p::'a)) (procedure_functor_type TYPE('a))"
  assumes procedure_functor_beta_reduced: "beta_reduced (procedure_functor_mk_untyped (p::'a))"
  assumes procedure_functor_mk_typed_inverse': 
    "well_typed_proc'' [] q (procedure_functor_type TYPE('a)) \<Longrightarrow> beta_reduced q
       \<Longrightarrow> procedure_functor_mk_untyped (procedure_functor_mk_typed' q) = q"
  assumes procedure_functor_mk_untyped_inverse':
    "procedure_functor_mk_typed' (procedure_functor_mk_untyped p) = p"

definition "procedure_functor_mk_typed p = procedure_functor_mk_typed' (beta_reduce p)"

lemma procedure_functor_mk_typed_inverse: 
    "well_typed_proc'' [] q (procedure_functor_type TYPE('a::procedure_functor))
       \<Longrightarrow> procedure_functor_mk_untyped (procedure_functor_mk_typed q :: 'a) = beta_reduce q"
  unfolding procedure_functor_mk_typed_def 
  apply (subst procedure_functor_mk_typed_inverse')
  apply (rule beta_reduce_preserves_well_typed, auto)
  apply (rule beta_reduce_def2)
  by (rule well_typed_beta_reduce)

lemma procedure_functor_mk_untyped_inverse:
    "procedure_functor_mk_typed (procedure_functor_mk_untyped p) = p"
  unfolding procedure_functor_mk_typed_def
  apply (subst beta_reduced_beta_reduce_id)
  close (fact procedure_functor_beta_reduced)
  by (fact procedure_functor_mk_untyped_inverse')


lemma procedure_functor_mk_untyped_injective:
    "procedure_functor_mk_untyped p = procedure_functor_mk_untyped q \<Longrightarrow> p = q"
using procedure_functor_mk_untyped_inverse by metis

typedef ('a::procedure_functor,'b::procedure_functor) procfun = "{p::procedure_rep.
  well_typed_proc'' [] p (ProcTFun (procedure_functor_type TYPE('a)) (procedure_functor_type TYPE('b)))
  \<and> beta_reduced p}"
  apply (rule exI[of _ "ProcAbs (procedure_functor_mk_untyped (undefined::'b))"], auto)
  apply (rule wt_ProcAbs, rule well_typed_extend, rule procedure_functor_welltyped)
  by (metis beta_reduced_def brc_ProcAbs procedure_functor_beta_reduced)

type_notation "procfun" (infixr "=proc=>" 0)

instantiation procfun :: (procedure_functor,procedure_functor) procedure_functor begin
definition [simp]: "procedure_functor_type (_::('a,'b)procfun itself)
     == ProcTFun (procedure_functor_type TYPE('a)) (procedure_functor_type TYPE('b))"
definition "procedure_functor_mk_untyped == Rep_procfun"
definition "procedure_functor_mk_typed' == Abs_procfun"
instance apply intro_classes 
  unfolding procedure_functor_type_procfun_def procedure_functor_mk_untyped_procfun_def
            procedure_functor_mk_typed'_procfun_def
  using Rep_procfun close auto
  close (metis Rep_procfun mem_Collect_eq)
  using Rep_procfun_inverse apply auto
  by (smt2 Abs_procfun_inverse mem_Collect_eq well_typed_extend(2))
end

instantiation prod :: (procedure_functor,procedure_functor) procedure_functor begin
definition [simp]: "procedure_functor_type (_::('a*'b) itself)
     == ProcTPair (procedure_functor_type TYPE('a)) (procedure_functor_type TYPE('b))"
definition "procedure_functor_mk_untyped == (\<lambda>(x,y). ProcPair (procedure_functor_mk_untyped x) (procedure_functor_mk_untyped y))"
definition "procedure_functor_mk_typed' p == (case p of ProcPair x y \<Rightarrow> (procedure_functor_mk_typed' x, procedure_functor_mk_typed' y))"
instance apply intro_classes 
  unfolding procedure_functor_type_prod_def procedure_functor_mk_untyped_prod_def
            procedure_functor_mk_typed'_prod_def
  close (auto, rule well_typed''_well_typed_proc''.intros, simp_all add: procedure_functor_welltyped)
  apply (case_tac p, clarify)
  apply (auto simp: beta_reduced_def, erule beta_reduce_proc.cases, auto)[]
    using procedure_functor_beta_reduced unfolding beta_reduced_def close auto
    using procedure_functor_beta_reduced unfolding beta_reduced_def close auto
  defer
  close (auto simp: procedure_functor_mk_untyped_inverse')[]
  apply (ind_cases "well_typed_proc'' [] q (ProcTPair a b)" for q a b, auto)
  sorry
end

instantiation procedure_ext :: (procargs,prog_type,singleton) procedure_functor begin
definition [simp]: "procedure_functor_type (_::('a,'b,'c)procedure_ext itself) == ProcTSimple (procedure_type TYPE(('a,'b,'c)procedure_ext))"
definition "procedure_functor_mk_untyped == mk_procedure_untyped"
definition "procedure_functor_mk_typed' == mk_procedure_typed"
instance proof intro_classes
  show "\<And>p::('a, 'b, 'c) procedure_scheme. well_typed_proc'' [] (procedure_functor_mk_untyped p)
          (procedure_functor_type TYPE(('a, 'b, 'c) procedure_scheme))"
    unfolding procedure_functor_type_procedure_ext_def procedure_functor_mk_untyped_procedure_ext_def 
    using well_typed_proc_well_typed_proc'' mk_procedure_untyped by metis
  show "\<And>p::('a, 'b, 'c) procedure_scheme. beta_reduced (procedure_functor_mk_untyped p)" 
    unfolding procedure_functor_mk_untyped_procedure_ext_def 
    using well_typed_proc_beta_reduced mk_procedure_untyped by auto
  show "\<And>q. well_typed_proc'' [] q (procedure_functor_type TYPE(('a, 'b, 'c) procedure_scheme)) \<Longrightarrow>
         beta_reduced q \<Longrightarrow> procedure_functor_mk_untyped (procedure_functor_mk_typed' q::('a, 'b, 'c) procedure_scheme) = q"
  proof -
    fix q assume wtq: "well_typed_proc'' [] q (procedure_functor_type TYPE(('a, 'b, 'c) procedure_scheme))"
    assume betaq: "beta_reduced q"
    obtain body args ret where q:"q = Proc body args ret"
      apply (rule_tac p=q in well_typed_ProcTSimple_Proc) 
        close (rule wtq[unfolded procedure_functor_type_procedure_ext_def])
        close (rule betaq)
        by metis
    have wtq0: "well_typed_proc q" 
      apply (rule well_typed''_well_typed)
        close (rule wtq[unfolded procedure_functor_type_procedure_ext_def])
        by (rule betaq)  
    hence "well_typed body" unfolding q by simp
    moreover have "\<And>v. v \<in> set args \<Longrightarrow> \<not> vu_global v"
      by (metis wtq0 q well_typed_proc.simps(1))
    moreover have "distinct args"
      by (metis wtq0 q well_typed_proc.simps(1))
    moreover
    have pt_q: "proctype_of q = procedure_type TYPE(('a, 'b, 'c) procedure_scheme)"
      apply (rule well_typed_proc''_proctype_of)
        close (rule wtq[unfolded procedure_functor_type_procedure_ext_def])
        by (rule betaq)  
    have "args \<in> procargvars TYPE('a)" 
      apply (rule procedure_type_procargvars)
        close (fact pt_q[unfolded q])
        by (fact wtq0[unfolded q])
    moreover have "eu_type ret = Type TYPE('b)" 
      using pt_q by (simp add: q procedure_type_def)
    ultimately show "procedure_functor_mk_untyped (procedure_functor_mk_typed' q::('a, 'b, 'c) procedure_scheme) = q"
      unfolding procedure_functor_mk_untyped_procedure_ext_def procedure_functor_mk_typed'_procedure_ext_def q
      by (subst mk_procedure_typed_inverse, auto)
  qed
  show "\<And>p::('a, 'b, 'c) procedure_scheme. 
        procedure_functor_mk_typed' (procedure_functor_mk_untyped p) = p"
    unfolding procedure_functor_mk_untyped_procedure_ext_def procedure_functor_mk_typed'_procedure_ext_def
    by (rule mk_procedure_untyped_inverse)
qed

end

definition procfun_apply :: "('a::procedure_functor,'b::procedure_functor)procfun \<Rightarrow> 'a \<Rightarrow> 'b" where
   "procfun_apply f p = procedure_functor_mk_typed (apply_procedure (procedure_functor_mk_untyped f) (procedure_functor_mk_untyped p))"

subsection {* Support for defining typed procedure functors *}

definition "subst_prog1 (p::'a::procedure_functor) q pr ==
  well_typed'' [procedure_functor_type TYPE('a)] q \<and> Abs_program (beta_reduce' 
                  (subst_proc_in_prog 0 (procedure_functor_mk_untyped p) (beta_reduce' q))) = pr"
definition "subst_proc1 (p::'a::procedure_functor) q (pr::('b::procargs,'c::prog_type)procedure) == 
  well_typed_proc'' [procedure_functor_type TYPE('a)] q (ProcTSimple (procedure_type TYPE(('b,'c)procedure)))
  \<and> procedure_functor_mk_typed (subst_proc 0 (procedure_functor_mk_untyped p) (beta_reduce q)) = pr"

locale reduce_procfun begin


lemma apply1:
  fixes p body body0 retval args and arg_proc::"'a::procedure_functor"
  assumes subst: "subst_prog1 arg_proc body PROGRAM[\<guillemotleft>body0\<guillemotright>]"
  defines "p0==procedure_functor_mk_typed (ProcAbs (Proc body (Rep_procargvars args) (mk_expression_untyped retval)))"
  shows "procfun_apply p0 arg_proc = \<lparr> p_body=body0, p_args=args, p_return=retval \<rparr>"
proof -
  have wt1: "well_typed_proc'' [procedure_functor_type TYPE('a)]
     (Proc body (mk_procargvars_untyped args) (mk_expression_untyped retval))
     (ProcTSimple (procedure_type TYPE(('b, 'c) procedure)))"
    apply (subst wt_Proc_iff, auto simp: procedure_type_def)
    close (metis Abs_procargs_cases Rep_procargvars procargs_typematch procargs_typematch'')
    using assms unfolding subst_prog1_def close auto
    using Rep_procargvars procargvars_local close auto
    using Rep_procargvars procargvars_distinct by auto

  have wt2: "well_typed_proc'' [] (ProcAbs (Proc body (mk_procargvars_untyped args) (mk_expression_untyped retval)))
        (procedure_functor_type TYPE('a =proc=> ('b, 'c) procedure))" 
    apply simp apply (rule wt_ProcAbs) by (fact wt1)

  have wt_body: "well_typed'' [procedure_functor_type TYPE('a)] body"
    using subst unfolding subst_prog1_def by simp

  have wt_subst: "well_typed'' [] (subst_proc_in_prog 0 (procedure_functor_mk_untyped arg_proc) (beta_reduce' body))"
    apply (rule well_typed_subst_proc[where F="[]", simplified])
    close (rule procedure_functor_welltyped)
    apply (rule beta_reduce_preserves_well_typed)
    by (rule wt_body)

  have aux: "Rep_program (Abs_program (beta_reduce' (subst_proc_in_prog 0 
             (procedure_functor_mk_untyped arg_proc) (beta_reduce' body)))) = Rep_program body0"
    using subst unfolding subst_prog1_def program_def by auto
  have subst': "beta_reduce' (subst_proc_in_prog 0 (procedure_functor_mk_untyped arg_proc)
                    (beta_reduce' body)) = mk_program_untyped body0"
    apply (subst Abs_program_inverse[symmetric], auto)
    apply (rule well_typed''_well_typed)
    close (metis beta_reduce_preserves_well_typed(1) wt_subst)
    apply (rule beta_reduce'_def2)
    close (metis beta_reduce_proofs.well_typed_beta_reduce(1) wt_subst)
    by (rule aux)

  show ?thesis
    unfolding p0_def procfun_apply_def apply_procedure_def
    apply (subst procedure_functor_mk_typed_inverse)
      close (fact wt2)
    apply (subst beta_reduce_ProcAbs)
      close (fact wt1)
    apply (subst beta_reduce_beta) 
      close (rule beta_reduce_preserves_well_typed, fact wt1)
      close (rule procedure_functor_welltyped)
    apply (rule procedure_functor_mk_untyped_injective)
    apply (subst procedure_functor_mk_typed_inverse)
      apply (rule beta_reduce_preserves_well_typed)
      apply (rule well_typed_subst_proc(2)[where F="[]", simplified])
        close (fact procedure_functor_welltyped)  
      apply (rule beta_reduce_preserves_well_typed(2)[where T="procedure_functor_type TYPE(('b,'c)procedure)"])
      apply (simp add: procedure_type_def)
      close (metis procedure_type_def wt1)
    apply (subst beta_reduce_Proc)
      close (fact wt_body)
    unfolding procedure_functor_mk_untyped_procedure_ext_def mk_procedure_untyped_def
    apply simp
    apply (subst beta_reduce_Proc)
      close (fact wt_subst)
    apply simp      
    by (fact subst')
qed

print_sorry apply1


lemma seq:
  assumes "subst_prog1 p q1 PROGRAM[\<guillemotleft>c1\<guillemotright>]"
  assumes "subst_prog1 p q2 PROGRAM[\<guillemotleft>c2\<guillemotright>]"
  defines "q == Seq q1 q2"
  shows "subst_prog1 p q PROGRAM[\<guillemotleft>c1\<guillemotright>; \<guillemotleft>c2\<guillemotright>]"
sorry

lemma closed:
  fixes q c p
  defines "q == mk_program_untyped c"
  shows "subst_prog1 p q PROGRAM[\<guillemotleft>c\<guillemotright>]"
sorry

lemma callproc:
  fixes v args q
  assumes "subst_proc1 p q r"
  defines "q0==CallProc (mk_variable_untyped v) q (mk_procargs_untyped procargs_empty)"
  shows "subst_prog1 p q0  PROGRAM[v:=call r()]"
sorry

lemma left: 
  assumes "subst_proc1 l q p"
  defines "q0 == ProcAppl (ProcAbs q) (ProcUnpair True (ProcRef 0))"
  shows "subst_proc1 (l, r) q0 p"
sorry

lemma procref: 
  defines "q0 == ProcRef 0"
  shows "subst_proc1 p q0 p"
sorry

lemma right: 
  assumes "subst_proc1 r q p"
  defines "q0 == ProcAppl (ProcAbs q) (ProcUnpair False (ProcRef 0))"
  shows "subst_proc1 (l, r) q0 p"
sorry

lemmas safe = apply1 closed seq procref callproc
lemmas unsafe = left right
lemmas reduce = safe unsafe

end

definition "x == Variable ''x'' :: int variable"
definition "y == Variable ''y'' :: unit variable"

schematic_lemma (in reduce_procfun) l1:
  shows "\<And>p q r. my_proc == ?my_proc \<Longrightarrow> 
  (procfun_apply my_proc (p,q,r) = proc() { x:=1; y:=call p(); y:=call q(); return () })"
apply (drule meta_eq_to_obj_eq, hypsubst, thin_tac "?a = ?b")
by (rule reduce)+

definition my_proc_def0: "my_proc \<equiv>
 procedure_functor_mk_typed
  (ProcAbs
    (Proc (Seq (Seq (mk_program_untyped (assign x (const_expression 1)))
                 (CallProc (mk_variable_untyped y)
                   (ProcAppl (ProcAbs (ProcRef 0)) (ProcUnpair True (ProcRef 0)))
                   (mk_procargs_untyped procargs_empty)))
            (CallProc (mk_variable_untyped y)
              (ProcAppl (ProcAbs (ProcAppl (ProcAbs (ProcRef 0)) (ProcUnpair True (ProcRef 0))))
                (ProcUnpair False (ProcRef 0)))
              (mk_procargs_untyped procargs_empty)))
      (mk_procargvars_untyped procargvars_empty) (mk_expression_untyped (const_expression ()))))"

lemmas my_proc_def = my_proc_def0[THEN reduce_procfun.l1]
