theory Modules
imports Lang_Typed TermX_Antiquot Procedures
begin


(*
lemma list_all2_mono' [mono]: "A \<le> B \<Longrightarrow> list_all2 A \<le> list_all2 B"
  apply auto unfolding list_all2_iff by auto
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
    (*have nth: "nth_opt (F @ T # E) (length F) = Some T"
      by (induct F, auto)
    have nth2: "\<And>n. length F < n \<Longrightarrow> nth_opt (F@T#E) n = nth_opt (F@E) (n - Suc 0)"
      apply (induct F arbitrary: n, case_tac n, auto)
      apply (case_tac n, auto)
      by (metis Suc_pred gr0_conv_Suc lessE nth_opt.simps(2)) 
    have nth3: "n < length F \<Longrightarrow> nth_opt (F@T#E) n = nth_opt (F @ E) n"
      apply (induct F arbitrary: n, auto)
      by (case_tac n, auto)*)
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
      (*have nth: "nth_opt (F @ T # E) (length F) = Some T"
        by (induct F, auto)
      have tmp: "\<And>x l m. x#l@m = (x#l)@m" by auto
      have nth2: "length F < n \<Longrightarrow> nth_opt (F@T#E) n = nth_opt (F@E) (n - Suc 0)"
        apply (induct F arbitrary: n, case_tac n, auto)
        apply (case_tac n, auto)
        by (metis Suc_pred gr0_conv_Suc lessE nth_opt.simps(2)) 
      have nth3: "n < length F \<Longrightarrow> nth_opt (F@T#E) n = nth_opt (F @ E) n"
        apply (induct F arbitrary: n, auto)
        by (case_tac n, auto)*)
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




definition "module_type_rep_set envT proctypes \<equiv> {procs. list_all2 (\<lambda>T p. well_typed_proc'' [] p (ProcFun' envT (ProcSimple T))) proctypes procs}"
lemma module_type_rep_set_inhabited: "\<exists>x. x \<in> module_type_rep_set env procT"
  sorry

class module_type =
  fixes "module_type_procs" :: "'a \<Rightarrow> procedure_rep list"
  fixes "module_type_construct" :: "procedure_rep list \<Rightarrow> 'a"
  fixes "module_type_proc_names" :: "'a itself \<Rightarrow> id list"
  fixes "module_type_proc_types" :: "'a itself \<Rightarrow> procedure_type list"
  fixes "module_type_environment" :: "'a itself \<Rightarrow> procedure_type_open list"
  assumes "distinct (module_type_proc_names TYPE('a))"
  assumes "length (module_type_procs a) = length (module_type_proc_names TYPE('a))"
  assumes module_type_procs_welltyped: "list_all2 
          (\<lambda>T p. well_typed_proc'' [] p (ProcFun' (module_type_environment TYPE('a)) (ProcSimple T)))
          (module_type_proc_types TYPE('a)) (module_type_procs m)"
  assumes module_type_construct_inverse: 
      "list_all2 
          (\<lambda>T p. well_typed_proc'' [] p (ProcFun' (module_type_environment TYPE('a)) (ProcSimple T)))
          (module_type_proc_types TYPE('a)) procs
      \<Longrightarrow> module_type_procs (module_type_construct procs) = procs"
  assumes module_type_procs_inverse: "module_type_construct (module_type_procs m) = m"

class module_type_closed = module_type +
  assumes closed_module_type_empty: "module_type_environment TYPE('a) = []"


definition "module_type_proc_types_open MT \<equiv> 
  map (\<lambda>T. foldr ProcFun (module_type_environment MT) (ProcSimple T)) (module_type_proc_types MT)"


definition "module_type_instantiation (_::'mt::module_type itself) (_::'mtc::module_type_closed itself)
  == module_type_proc_names TYPE('mt) = module_type_proc_names TYPE('mtc)
   \<and> module_type_proc_types TYPE('mt) = module_type_proc_types TYPE('mtc)" 





ML_file "modules.ML"


setup {*
fn thy => thy |> snd o
Modules.define_module_type {
  name = @{binding MT},
  arguments = [],
  procs = [{name = @{binding a}, typ = @{typ "(unit,int)procedure"}},
           {name = @{binding b}, typ = @{typ "(int*unit,int)procedure"}}]
}*}

thm MT.MAKE.b

(* TODO move *)
lemma mk_procedure_untyped_inverse [simp]: 
  "mk_procedure_typed (mk_procedure_untyped p) = p"
  SORRY

declare[[simp_trace=false]]
(*definition "MT_make == \<lambda>(p1::(unit,int)procedure) (p2::(int*unit,int)procedure).
  Abs_MT [mk_procedure_untyped p1, mk_procedure_untyped p2]"*)
(*lemma MT_MAKE_a: "MT.a (MT.MAKE a b) = a"
  apply (unfold MT.a_def MT.MAKE_def module_type_procs_MT_def)
  apply (subst Abs_MT_inverse)
  (* First goal *)
  (* apply (simp only: list.simps Set.ball_simps HOL.simp_thms Modules.proctype_of_mk_procedure_untyped) *)
  apply (simp add: subst_proc_empty module_type_rep_set_def)
  (* Second goal *)
  apply (simp add: subst_proc_empty)
done*)

lemma "MT.b (MT.MAKE undefined undefined) = undefined" by simp

thm MT.MAKE.a

declare[[ML_exception_trace=false]]

setup {* fn thy => thy |> 
Modules.define_module_type {
  name = @{binding MT2},
  procs = [{name = @{binding b}, typ = @{typ "(bool*unit,bool)procedure"}}],
  arguments = [{name = @{binding M}, typ = @{typ "MT"}}] 
} |> snd*}

thm MT2.INST_def


declare[[show_consts]]
thm MT2.INST_def
(*definition "MT2_INST == \<lambda>MT2::MT2. \<lambda>MT::MT.
  Abs_MT2_instantiated (map (subst_proc (module_type_procs MT)) (module_type_procs MT2))" *)
lemma "MT2_instantiated.b (MT2.INST MT2 MT) = MT2.b MT2 MT"
  unfolding MT2.INST_def MT2_instantiated.b_def
  apply (subst module_type_construct_inverse)
  unfolding module_type_proc_types_MT2_instantiated_def
  apply simp 
  using module_type_procs1 module_type_procs2
  apply auto
  sorry


thm Rep_MT2
thm module_type_environment_MT2_def

declare[[show_consts]]

lemma 
  fixes n::nat and M::"'mt::module_type"
  assumes inst: "module_type_instantiation TYPE('mt) TYPE('mtc::module_type_closed)"
(*  assumes "length (module_type_procs M) > n" *)
  shows "mk_procedure_typed (subst_proc [] (module_type_procs
         (module_type_construct (map (subst_proc procs) (module_type_procs M)) :: 'mtc)!n)) =
    mk_procedure_typed (subst_proc procs (module_type_procs M!n))"
proof -
  note mt_procT_same = inst[unfolded module_type_instantiation_def, THEN conjunct2, symmetric]
  have pt_of: "\<And>p. p\<in>set (module_type_procs M) \<Longrightarrow> proctype_of (subst_proc procs p) = proctype_of p"
    sorry
  have "module_type_procs (module_type_construct (map (subst_proc procs) (module_type_procs M)) :: 'mtc)
      = map (subst_proc procs) (module_type_procs M)"
      apply (subst module_type_construct_inverse)
      (* Goal 1 *)
      unfolding mt_procT_same module_type_procs1[of M, symmetric]
      using pt_of apply auto[1]
      (* Goal 2 *)
      unfolding closed_module_type_empty
  let ?inst = "Abs_MT_inst (map (subst_proc procs) (module_type_procs M))"
  have len: "length (module_type_procs ?inst) > n" sorry
  have subst: "subst_proc [] (module_type_procs ?inst!n) = module_type_procs ?inst!n"
    apply (subst subst_proc_empty) 
    apply (rule module_type_procs_welltyped[where m="Abs_MT_inst (map (subst_proc procs) (module_type_procs M))", unfolded closed_module_type_empty])
    using len by auto
  show ?thesis
    unfolding subst apply (subst Abs_MT_inst_inverse)
    unfolding module_type_rep_set_def apply auto
    
    thm Abs_MT2_inverse
    apply (subst)


(* TODO: *)
lemma "MT2_instantiated.b (MT2.INST MT2 MT) = MT2.b MT2 MT"
  unfolding MT2_instantiated.b_def MT2.INST_def MT2.b_def
  apply (subst subst_proc_empty)
  unfolding module_type_procs_MT2_def module_type_procs_MT2_instantiated_def
  apply (subst Abs_MT2_instantiated_inverse)
  apply (rule tmp1) using Rep_MT2 apply simp
  using Rep_MT2 unfolding module_type_rep_set_def 

ML {* !Modules.last_defined_module_type |> the |> (fn Modules.ModTypeInfo x => x)
  |> #getters |> hd |> #thm |> rep_thm
*}

typ MT2_instantiated

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

thm Abs_MT3_inverse
thm MT3.x_def
thm MT3.INST_def

