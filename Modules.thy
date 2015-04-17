theory Modules
imports Lang_Typed TermX_Antiquot Procedures
begin

(* TODO: 

- Define MT.MAKE also for non-closed modules (using procfun-type)
- Define getters also for non-closed modules (using procfun-type)
*)

lemma well_typed_lift_same:
  assumes "i\<ge>length E"
  shows "well_typed'' E pg \<Longrightarrow> lift_proc_in_prog pg i = pg"
    and "well_typed_proc'' E p T \<Longrightarrow> lift_proc p i = p"
proof -
  show r1: "well_typed'' E pg \<Longrightarrow> i\<ge>length E \<Longrightarrow> lift_proc_in_prog pg i = pg"
    and r2: "well_typed_proc'' E p T \<Longrightarrow> i\<ge>length E \<Longrightarrow> lift_proc p i = p"
  by (induct arbitrary: i and i rule:well_typed''_well_typed_proc''.inducts, auto)
qed (auto simp: assms)

lemma well_typed_lift:
  assumes "well_typed_proc'' (F@E) q T"
  shows "well_typed_proc'' (F@U#E) (lift_proc q (length F)) T"
proof -
  have "\<And>T F. well_typed'' (F@E) pg \<Longrightarrow> well_typed'' (F@T#E) (lift_proc_in_prog pg (length F))"
   and res:"\<And>T U F. well_typed_proc'' (F@E) q U \<Longrightarrow> well_typed_proc'' (F@T#E) (lift_proc q (length F)) U"
  proof (induct pg and q) 
  case Assign thus ?case by (auto simp: wt_Assign_iff[symmetric])
  next case Sample thus ?case by (auto simp: wt_Sample_iff[symmetric])
  next case (Proc body args ret) thus ?case by (auto simp: wt_Proc_iff[symmetric])
  next case (CallProc v p a U) thus ?case by (auto simp: wt_CallProc_iff[symmetric])
  next case Seq thus ?case by (auto simp: wt_Seq_iff[symmetric])
  next case Skip thus ?case by (auto simp: wt_Skip)
  next case IfTE thus ?case by (auto simp: wt_IfTE_iff[symmetric])
  next case While thus ?case by (auto simp: wt_While_iff[symmetric])
  next case (ProcRef n)
    from ProcRef show ?case by (auto simp: wt_ProcRef_iff[symmetric] nth_append)
  next case (ProcAbs p T U) 
    from ProcAbs.prems obtain U1 U2 where U:"U=ProcFun U1 U2"
      and wt: "well_typed_proc'' (U1#F@E) p U2"
      unfolding wt_ProcAbs_iff[symmetric] by auto
    show ?case apply (simp add: wt_ProcAbs_iff[symmetric]) 
      apply (rule exI[of _ U1], rule exI[of _ U2], simp add: U)
      apply (rule ProcAbs.hyps[where F="U1#F" and T=T and U=U2, simplified])
      by (fact wt)
  next case (ProcAppl p1 p2 ) thus ?case by (auto simp: wt_ProcAppl_iff[symmetric], metis)
  qed
  from res assms show ?thesis .
qed
  
lemma well_typed_subst':
  assumes "well_typed_proc'' (F@E) q T"
  shows "well_typed'' (F@T#E) pg \<Longrightarrow> well_typed'' (F@E) (subst_proc_in_prog (length F) q pg)"
  and "well_typed_proc'' (F@T#E) p U \<Longrightarrow> well_typed_proc'' (F@E) (subst_proc (length F) q p) U"
proof -
  have res:"\<And>T E F q.
    well_typed'' (F@T#E) pg \<Longrightarrow>
    well_typed_proc'' (F@E) q T \<Longrightarrow>
    well_typed'' (F@E) (subst_proc_in_prog (length F) q pg)"
   and  "\<And>T U E F q.
    well_typed_proc'' (F@T#E) p U \<Longrightarrow>
    well_typed_proc'' (F@E) q T \<Longrightarrow>
    well_typed_proc'' (F@E) (subst_proc (length F) q p) U"
  proof (induct pg and p)
    case Assign thus ?case by (auto simp: wt_Assign_iff[symmetric])
    next case Sample thus ?case by (auto simp: wt_Sample_iff[symmetric])
    next case Proc thus ?case by (auto simp: wt_Proc_iff[symmetric])
    next case (ProcRef n) 
      from ProcRef show ?case by (auto simp: wt_ProcRef_iff[symmetric] nth_append)
    next case (ProcAppl p1 p2)
      from ProcAppl.prems(1) obtain T' where 
        wt1: "well_typed_proc'' (F@T#E) p1 (ProcFun T' U)" and wt2: "well_typed_proc'' (F@T#E) p2 T'"
        unfolding wt_ProcAppl_iff[symmetric] by auto
      have wt1': "well_typed_proc'' (F@E) (subst_proc (length F) q p1) (ProcFun T' U)"
        by (rule ProcAppl, rule wt1, rule ProcAppl)
      have wt2': "well_typed_proc'' (F@E) (subst_proc (length F) q p2) T'"
        by (rule ProcAppl, rule wt2, rule ProcAppl)
      show ?case apply simp
        unfolding wt_ProcAppl_iff[symmetric] apply (rule exI[of _ T']) using wt1' wt2' by auto
    next case Seq thus ?case by (auto simp: wt_Seq_iff[symmetric])
    next case Skip show ?case by (simp, rule wt_Skip)
    next case IfTE thus ?case by (auto simp: wt_IfTE_iff[symmetric])
    next case While thus ?case by (auto simp: wt_While_iff[symmetric])
    next case CallProc thus ?case by (auto simp: wt_CallProc_iff[symmetric])
    next case (ProcAbs p)
      from ProcAbs.prems obtain T' U' where U: "U = ProcFun T' U'" and wt: "well_typed_proc'' (T' # F @ T # E) p U'" 
        unfolding wt_ProcAbs_iff[symmetric] by auto  
      show ?case apply simp
        unfolding wt_ProcAbs_iff[symmetric]
        apply (rule exI[of _ T'], rule exI[of _ U'], auto simp: U wt)
        apply (rule ProcAbs.hyps[of "T'#F", simplified])
        apply (fact wt) 
        apply (rule well_typed_lift[where F="[]", simplified])
        by (fact ProcAbs.prems)
    qed
  with assms
  show "well_typed'' (F@T#E) pg \<Longrightarrow> well_typed'' (F@E) (subst_proc_in_prog (length F) q pg)"
  and "well_typed_proc'' (F@T#E) p U \<Longrightarrow> well_typed_proc'' (F@E) (subst_proc (length F) q p) U"
    by auto
qed

lemma well_typed_subst:
  assumes "well_typed_proc'' (F@E) q T"
  assumes "well_typed'' (F@T#E) pg"
  shows "well_typed'' (F@E) (subst_proc_in_prog (length F) q pg)"
using assms by (rule well_typed_subst')

lemma well_typed_proc_subst:
  assumes "well_typed_proc'' (F@E) q T"
  assumes "well_typed_proc'' (F@T#E) p U"
  shows "well_typed_proc'' (F@E) (subst_proc (length F) q p) U"
using assms by (rule well_typed_subst')

definition "module_type_rep_set envT proctypes \<equiv> {procs. list_all2 (\<lambda>T p. well_typed_proc'' [] p (foldr ProcFun envT (ProcSimple T))) proctypes procs}"
lemma module_type_rep_set_inhabited: "\<exists>x. x \<in> module_type_rep_set env procT"
  sorry

class module_type =
  fixes "module_type_procs" :: "'a \<Rightarrow> procedure_rep list"
  fixes "module_type_construct" :: "procedure_rep list \<Rightarrow> 'a"
  fixes "module_type_proc_names" :: "'a itself \<Rightarrow> id list"
  fixes "module_type_proc_types" :: "'a itself \<Rightarrow> procedure_type list"
  fixes "module_type_environment" :: "'a itself \<Rightarrow> procedure_type_open list"
  assumes module_type_proc_names_distict: "distinct (module_type_proc_names TYPE('a))"
  assumes module_type_procs_length: "length (module_type_procs a) = length (module_type_proc_names TYPE('a))"
  assumes module_type_procs_welltyped: "list_all2 
          (\<lambda>T p. well_typed_proc'' [] p (foldr ProcFun (module_type_environment TYPE('a)) (ProcSimple T)))
          (module_type_proc_types TYPE('a)) (module_type_procs m)"
  assumes module_type_construct_inverse: 
      "list_all2 
          (\<lambda>T p. well_typed_proc'' [] p (foldr ProcFun (module_type_environment TYPE('a)) (ProcSimple T)))
          (module_type_proc_types TYPE('a)) procs
      \<Longrightarrow> module_type_procs (module_type_construct procs) = procs"
  assumes module_type_procs_inverse: "module_type_construct (module_type_procs m) = m"

class module_type_closed = module_type +
  assumes closed_module_type_empty: "module_type_environment TYPE('a) = []"


definition "module_type_proc_types_open (_::'a::module_type itself) \<equiv> 
  map (\<lambda>T. foldr ProcFun (module_type_environment TYPE('a)) (ProcSimple T)) (module_type_proc_types TYPE('a))"

lemma module_type_procs_welltyped': "list_all2 
          (\<lambda>T p. well_typed_proc'' [] p T) (module_type_proc_types_open TYPE('a::module_type)) (module_type_procs (m::'a))"
  unfolding module_type_proc_types_open_def apply (subst list_all2_map1)
  by (fact module_type_procs_welltyped)

definition "module_type_instantiation (_::'mt::module_type itself) (_::'mtc::module_type_closed itself)
  == module_type_proc_names TYPE('mt) = module_type_proc_names TYPE('mtc)
   \<and> module_type_proc_types TYPE('mt) = module_type_proc_types TYPE('mtc)" 


definition "instantiate_procedure args p = fold (\<lambda>a p. apply_procedure p a) args p"


(* We need to remove const constraints for the next lemma. Is there a cleaner way? *)
ML {*  
  val consts_to_unconstrain = [@{const_name module_type_procs},
                               @{const_name module_type_construct},
                               @{const_name module_type_proc_names},
                               @{const_name module_type_proc_types},
                               @{const_name module_type_environment}];
  val consts_orig_constraints = map (Sign.the_const_constraint @{theory}) consts_to_unconstrain
*}
setup {*
  fold (fn c => fn thy => Sign.add_const_constraint (c,NONE) thy) consts_to_unconstrain
*}

declare[[show_types=false]]
lemma OFCLASS_module_type: 
  fixes procs construct proc_names proc_types environment

  (* These are directly instantiated with the various theorems generated by
     the definitional tools used for defining the module type *)
  assumes module_type_procs: "module_type_procs::'a\<Rightarrow>_ == procs"
  assumes module_type_construct: "module_type_construct::_\<Rightarrow>'a == construct"
  assumes module_type_proc_names: "module_type_proc_names == \<lambda>_\<Colon>'a itself. proc_names"
  assumes module_type_proc_types: "module_type_proc_types == \<lambda>_\<Colon>'a itself. proc_types"
  assumes module_type_environment: "module_type_environment == \<lambda>_\<Colon>'a itself. environment"
  assumes Rep: "\<And>m. procs (m\<Colon>'a) \<in> module_type_rep_set environment proc_types"
  assumes Rep_inverse: "\<And>m. construct (procs m) = m"
  assumes Abs_inverse: "\<And>m. m \<in> module_type_rep_set environment proc_types \<Longrightarrow> procs (construct m) = m"

  (* These need to be proven. "simp" should solve all of them once automatically. *)
  assumes distinct: "distinct proc_names"
  assumes length: "length proc_names = length proc_types"
  shows "OFCLASS('a, module_type_class)"
proof intro_classes
  show "distinct (module_type_proc_names TYPE('a))"
    unfolding module_type_proc_names using distinct by simp
  fix m::'a
  have "length (module_type_procs m) = length (module_type_proc_types TYPE('a))"
    unfolding module_type_procs module_type_proc_types
    using Rep unfolding module_type_rep_set_def apply auto
    by (metis list_all2_conv_all_nth)
  thus "length (module_type_procs m) = length (module_type_proc_names TYPE('a))"
    unfolding module_type_proc_types module_type_proc_names
    using length by auto
  show "list_all2 (\<lambda>T p. well_typed_proc'' [] p (foldr ProcFun (module_type_environment TYPE('a)) (ProcSimple T)))
          (module_type_proc_types TYPE('a)) (module_type_procs m)"
    unfolding module_type_environment module_type_proc_types module_type_procs
    using Rep unfolding module_type_rep_set_def by auto
  show "module_type_construct (module_type_procs m) = m"
    unfolding module_type_construct module_type_procs
    by (fact Rep_inverse)
  fix ps
  assume in_rep_set: "list_all2 (\<lambda>T p. well_typed_proc'' [] p (foldr ProcFun (module_type_environment TYPE('a)) (ProcSimple T)))
              (module_type_proc_types TYPE('a)) ps"
  show "module_type_procs (module_type_construct ps :: 'a) = ps"
    unfolding module_type_procs module_type_construct
    apply (rule Abs_inverse) using in_rep_set 
    unfolding module_type_rep_set_def module_type_environment module_type_proc_types
    by simp
qed

declare[[show_types=false]]
lemma OFCLASS_module_type_closed: 
  fixes environment
  assumes module_type_environment: "module_type_environment == \<lambda>_\<Colon>'a itself. []"
  assumes module_type: "OFCLASS('a, module_type_class)"
  shows "OFCLASS('a, module_type_closed_class)"
unfolding module_type_closed_class_def 
  unfolding class.module_type_closed_axioms_def unfolding assms using assms 
  by simp_all


(* Recover stored type constraints *)
setup {*
  fold2 (fn c => fn T => fn thy => Sign.add_const_constraint (c,SOME (Logic.unvarifyT_global T)) thy)
      consts_to_unconstrain consts_orig_constraints
*}




ML_file "modules.ML"


setup {*
fn thy => thy |> snd o
Modules.define_module_type {
  name = @{binding MT},
  arguments = [],
  procs = [{name = @{binding a}, typ = @{typ "(unit,int)procedure"}},
           {name = @{binding b}, typ = @{typ "(int*unit,int)procedure"}}]
}*}

(* TODO: move *)
lemma mk_expression_untyped_inverse: "mk_expression_typed (mk_expression_untyped e) = e"
  unfolding mk_expression_typed_def mk_expression_untyped_fun
            mk_expression_untyped_type embedding_inv' e_fun_def
  apply simp unfolding e_vars_def
  by (metis (full_types) Rep_expression_inverse expression_rep.surjective old.unit.exhaust)

  
(* TODO: move *)
lemma mk_procedure_untyped_inverse: "mk_procedure_typed (mk_procedure_untyped p) = p"
  unfolding mk_procedure_untyped_def apply simp
  unfolding Rep_program_inverse Rep_procargvars_inverse  mk_expression_untyped_inverse
  by auto

(* TODO: automate this proof *)
lemma "MT.b (MT.MAKE a b) = b"
unfolding MT.b_def MT.MAKE_def
apply (subst module_type_construct_inverse)
unfolding module_type_proc_types_MT_def module_type_environment_MT_def apply auto
using procedure_functor_welltyped[of a]
unfolding procedure_functor_type_procfun_def procedure_functor_type_procedure_ext_def
apply simp
using procedure_functor_welltyped[of b]
unfolding procedure_functor_type_procfun_def procedure_functor_type_procedure_ext_def
apply simp
unfolding instantiate_procedure_def procedure_functor_mk_untyped_procedure_ext_def
apply simp
by (rule mk_procedure_untyped_inverse)


setup {* fn thy => thy |> 
Modules.define_module_type {
  name = @{binding MT2},
  procs = [{name = @{binding b}, typ = @{typ "(bool*unit,bool)procedure"}}],
  arguments = [{name = @{binding M}, typ = @{typ "MT"}},{name = @{binding MX}, typ = @{typ "MT"}}] 
} |> snd*}
print_theorems

lemma instantiate_procedure_nil: "instantiate_procedure [] x = x" unfolding instantiate_procedure_def by simp

lemma beta_reduce_preserves_type: "well_typed_proc'' E p T \<Longrightarrow> well_typed_proc'' E (beta_reduce p) T" sorry

lemma tmp:
  assumes "well_typed_proc'' [] p (foldr ProcFun Ts T)"
  assumes "list_all2 (\<lambda>T p. well_typed_proc'' [] p T) Ts ps"
  shows "well_typed_proc'' [] (instantiate_procedure ps p) T"
proof -
  {fix p p' T T'
   assume a:"well_typed_proc'' [] p' T'" and b:"well_typed_proc'' [] p (ProcFun T' T)"
   have "well_typed_proc'' [] (apply_procedure p p') T"
    unfolding apply_procedure_def
    apply (rule beta_reduce_preserves_type)
    apply (rule wt_ProcAppl) using a b by auto}
  note tmp = this
  show ?thesis
    using assms(2) assms(1) unfolding instantiate_procedure_def
    apply (induction Ts ps arbitrary: p rule:list_all2_induct, auto)
    by (metis tmp)
qed


lemma "MT2_instantiated.b (MT2.INST MT2 MT MTX) = MT2.b MT2 MT MTX"
  unfolding MT2.INST_def MT2_instantiated.b_def MT2.b_def
  unfolding instantiate_procedure_nil
  apply (subst module_type_construct_inverse)
  defer
  apply (subst List.nth_map) unfolding module_type_procs_length module_type_proc_names_MT2_def apply simp_all
  unfolding module_type_environment_MT2_instantiated_def apply simp
  unfolding module_type_proc_types_MT2_instantiated_def list_all2_map2

  using module_type_procs_welltyped[where m=MT2] unfolding module_type_proc_types_MT2_def
  apply (rule list_all2_mono) unfolding module_type_environment_MT2_def
  apply (rule_tac Ts="module_type_proc_types_open TYPE(MT) @ module_type_proc_types_open TYPE(MT)" in tmp, simp)
  apply (rule list_all2_appendI[OF module_type_procs_welltyped'])
  by (rule module_type_procs_welltyped')

setup {*
fn thy => thy |> snd o
Modules.define_module_type {
  name = @{binding MT3},
  procs = [{name = @{binding x}, typ = @{typ "(bool*unit,string)procedure"}},
           {name = @{binding y}, typ = @{typ "(string*unit,string)procedure"}}],
  arguments = [{name = @{binding M}, typ = @{typ "MT"}},
               {name = @{binding M2}, typ = @{typ "MT2"}}] 
  };
*}

term MT3.MAKE term MT3.UNMAKE

