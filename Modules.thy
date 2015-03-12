theory Modules
imports Lang_Typed
begin

section {* Procedures with procedure arguments *}

(*
typedef ('a,'b) finite_map = "{m::'a\<rightharpoonup>'b. finite(dom m)}"
  by (metis (poly_guards_query) finite_dom_map_of mem_Collect_eq) 
*)

datatype module_type = ModuleType
 "(id0,module_type) map" (* args *)
 "(id,procedure_type) map" (* procedure types *)
fun mt_proctypes :: "module_type \<Rightarrow> (id,procedure_type) map" where
  "mt_proctypes (ModuleType _ pt) = pt"

fun module_type_map_to_proc_env :: "(id0,module_type) map \<Rightarrow> (id,procedure_type)map" where
  "module_type_map_to_proc_env T [] = None"
| "module_type_map_to_proc_env T (modul#path) =
    (case T modul of None \<Rightarrow> None
                   | Some (ModuleType args' procs') \<Rightarrow> procs' path)"
lemma module_type_map_to_proc_env_empty:
  "module_type_map_to_proc_env empty = empty"
  by (rule ext, rule list.induct, auto)

record module_rep =
  mr_module_args :: "(id0,module_type) map"
  mr_procs :: "(id,procedure_rep) map"
(* TODO variables *)

definition well_typed_module :: "module_rep \<Rightarrow> bool" where
  "well_typed_module m == finite(dom(mr_procs m)) \<and> finite(dom(mr_module_args m)) 
  \<and> (\<forall>p\<in>ran(mr_procs m). well_typed_proc' (module_type_map_to_proc_env(mr_module_args m)) p)"

typedef module = "{m. well_typed_module m}"
  by (rule exI[where x="\<lparr> mr_module_args=empty, mr_procs=empty \<rparr>"], auto simp: well_typed_module_def)
definition "get_proc_in_module M name = mr_procs (Rep_module M) name"

fun has_module_type' :: "module_rep \<Rightarrow> module_type \<Rightarrow> bool" where
  "has_module_type' modul (ModuleType argsT procsT) =
   (well_typed_module modul \<and> 
    mr_module_args modul = argsT \<and>
   (\<forall>name. case (procsT name, mr_procs modul name) of
      (Some procT, Some p) \<Rightarrow> (proctype_of p = procT)
    | (Some procT, None) \<Rightarrow> False
    | (None, _) \<Rightarrow> True))"

definition "has_module_type M == has_module_type' (Rep_module M)"

definition "is_closed_module modul == mr_module_args modul = empty"
fun is_closed_module_type where
 "is_closed_module_type (ModuleType args _) = (args = empty)"

lemma todo_name:
  fixes modul modulT name
  assumes modtype: "has_module_type' modul modulT"
  assumes progtype: "mt_proctypes modulT name = Some (procedure_type TYPE(('a::procargs,'b::prog_type)procedure))"
  assumes p_def: "mr_procs modul name = Some p"
  assumes concr: "is_concrete_proc p" (* Follows from closed *)
  assumes closed: "is_closed_module modul"
  shows "mk_procedure_untyped (mk_procedure_typed p::('a,'b)procedure) = p"
proof -
  obtain body args ret where p_def2: "p = Proc body args ret"
    by (metis concr is_concrete_proc.elims(2))
  obtain modargs procs where modulT_def: "modulT = ModuleType modargs procs" 
    by (cases modulT, auto)
  have "well_typed_module modul"
    using modtype apply (cases modulT) by auto
  have env: "module_type_map_to_proc_env(mr_module_args modul) = empty"
    apply (subst closed[unfolded is_closed_module_def])
    by (fact module_type_map_to_proc_env_empty)
  have wt_proc: "well_typed_proc' empty p"
    apply (subst env[symmetric])
    using `well_typed_module modul`[unfolded well_typed_module_def, THEN conjunct2, THEN conjunct2]
    apply (rule ballE[of _ _ p])
    unfolding p_def2 apply simp
    by (metis p_def p_def2 ranI) 
  from wt_proc have wt: "well_typed body"
    unfolding p_def2 by simp
  have proctype: "proctype_of p = procedure_type TYPE(('a::procargs,'b::prog_type)procedure)"
    using modtype unfolding modulT_def apply simp
    by (metis (mono_tags) modulT_def mt_proctypes.simps option.simps(5) p_def progtype)
  have args: "args \<in> procargvars TYPE('a)"
  proof -
    have rw: "procargtypes TYPE('a) = map vu_type args"
      using proctype unfolding p_def2 procedure_type_def by auto
    show ?thesis
    unfolding procargvars_def apply auto
    using wt_proc unfolding p_def2 apply simp
    unfolding rw list_all2_map2 apply (rule list_all2_refl, simp) 
    using wt_proc unfolding p_def2 apply auto
    by (metis list_all_iff)
  qed
  show "mk_procedure_untyped (mk_procedure_typed p::('a,'b)procedure) = p"
    unfolding p_def2 mk_procedure_untyped_def apply auto
    using wt apply (metis Abs_program_inverse mem_Collect_eq)
    using args apply (subst Abs_procargvars_inverse, auto)
    apply (subst mk_expression_typed_inverse, auto)
    using proctype unfolding procedure_type_def p_def2 by simp
qed


lemma module_proc_type:
  assumes name: "name \<in> dom procT"
  assumes type: "has_module_type M (ModuleType argT procT)"
  obtains p where "get_proc_in_module M name = Some p"
            and "well_typed_proc' (module_type_map_to_proc_env argT) p"
            and "Some (proctype_of p) = procT name"
proof -
  let ?M = "Rep_module M"
  have h: "case (procT name, mr_procs ?M name) of
      (Some procT, Some p) \<Rightarrow> (proctype_of p = procT)
    | (Some procT, None) \<Rightarrow> False
    | (None, _) \<Rightarrow> True"
  by (metis type has_module_type'.simps has_module_type_def)
  def p == "the (get_proc_in_module M name)"

  have "get_proc_in_module M name = Some p"
    by (smt2 h name domIff p_def get_proc_in_module_def option.case_eq_if option.collapse prod.case)  
  moreover have "well_typed_proc' (module_type_map_to_proc_env argT) p" 
  proof -
    have ran: "p \<in> ran (mr_procs (Rep_module M))"
      by (metis (mono_tags) p_def curryI curry_split domD get_proc_in_module_def h name option.collapse option.simps(4) option.simps(5) ranI)
    hence "well_typed_proc' (module_type_map_to_proc_env (mr_module_args ?M)) p"
      using type by (auto simp: well_typed_module_def has_module_type_def)
    also have "mr_module_args ?M = argT"
      using type by (auto simp: has_module_type_def)
    ultimately show ?thesis by simp
  qed
  moreover have "Some (proctype_of p) = procT name"
    by (smt2 calculation(1) domIff get_proc_in_module_def h name not_None_eq option.simps(5) prod.case)
  ultimately show ?thesis ..
qed


lemma module_proc_notref:
  assumes type: "has_module_type M (ModuleType empty procT)"
  assumes get: "get_proc_in_module M name = Some (ProcRef x y z)"
  shows False
proof -
  let ?M = "Rep_module M"
  let ?p = "ProcRef x y z"
  have wt: "well_typed_module ?M"
    by (metis Rep_module mem_Collect_eq)
  have args_empty: "mr_module_args ?M = empty"
    by (metis type has_module_type'.simps has_module_type_def)
  from get have ran: "?p\<in>ran (mr_procs (Rep_module M))"
    unfolding get_proc_in_module_def by (rule ranI)
  have "well_typed_proc' empty (ProcRef x y z)"
    using wt unfolding well_typed_module_def
    unfolding module_type_map_to_proc_env_empty[symmetric]
    by (metis (poly_guards_query) has_module_type'.simps has_module_type_def ran type)
  thus ?thesis by simp
qed

definition "get_proc_in_module' name modul = mk_procedure_typed (the (mr_procs (Rep_module modul) name))"

lemma get_proc_in_module':
  fixes M::module and procT name
  assumes type: "has_module_type M (ModuleType empty procT)"
  assumes procT: "procT name = Some (procedure_type TYPE(('a::procargs,'b::prog_type)procedure))"
  shows "get_proc_in_module M name =
    Some (mk_procedure_untyped (get_proc_in_module' name M::('a,'b)procedure))"
proof (cases "the (mr_procs (Rep_module M) name)")
case (ProcRef x y z)
  note procref = this
  show ?thesis apply (rule FalseE)
    by (metis domI get_proc_in_module_def module_proc_type module_proc_notref option.sel procT procref type)
(*  obtain p where somep: "get_proc_in_module M name = Some p"
    apply (rule module_proc_defined)
    apply (metis domI get_proc_in_module_def module_proc_defined module_proc_notref option.sel procT procref type)
    apply (rule name) apply (rule type) by auto
  with procref have someref: "get_proc_in_module M name = Some (ProcRef x y z)"
    by (metis get_proc_in_module_def option.sel)
  have False apply (rule module_proc_notref) 
    using assms apply simp by (fact someref) *)
next
case (Proc body args ret)
  note proc = this
  obtain p where get_proc: "get_proc_in_module M name = Some p"
             and wt_p_0: "well_typed_proc' (module_type_map_to_proc_env empty) p"
             and procT_name: "Some (proctype_of p) = procT name"
    using module_proc_type type procT by blast
  with proc have p_def: "p = (Proc body args ret)"
    unfolding get_proc_in_module_def by auto
  have empty_args: "mr_module_args (Rep_module M) = empty"
    by (metis has_module_type'.simps has_module_type_def type)
(*  have ran: "Proc body args ret \<in> ran (mr_procs (Rep_module M))"
    by (metis (full_types) domI get_proc_in_module_def module_proc_type option.collapse option.distinct(1) proc procT ranI type)  *)
(*  have "well_typed_module (Rep_module M)"
    by (metis Rep_module mem_Collect_eq)  *)

  with wt_p_0 have wt_p: "well_typed_proc' empty p" 
    unfolding module_type_map_to_proc_env_empty by simp

  have p_type: "proctype_of p = procedure_type TYPE(('a::procargs,'b::prog_type)procedure)"
    by (metis procT_name option.sel procT)

  show "get_proc_in_module M name =
       Some (mk_procedure_untyped (get_proc_in_module' name M::('a,'b)procedure))" 
    unfolding proc get_proc_in_module'_def
    apply (subst mk_procedure_typed_inverse)
    using wt_p p_def apply simp
    defer
    using p_type apply (simp add: p_def procedure_type_def)
    apply (simp add: get_proc p_def)
    using p_type wt_p unfolding p_def by (rule procedure_type_procargvars)
qed


section {* Some tests (TODO: remove) *}

(*
module type MT = {
  proc a(int) : bool
  proc b(int,int) : unit
}
*)

definition MT :: module_type where
"MT == ModuleType empty [[''a''] \<mapsto> procedure_type TYPE((int*unit,bool)procedure),
                         [''b''] \<mapsto> procedure_type TYPE((int*int*unit,unit)procedure)]"
typedef MT = "{m. has_module_type m MT}" sorry  

(* Only defined for closed module types *)
definition get_MT_a :: "module \<Rightarrow> (int*unit,bool) procedure" where
  "get_MT_a = get_proc_in_module' [''a'']"
definition get_MT_b :: "module \<Rightarrow> (int*int*unit,unit) procedure" where
  "get_MT_b = get_proc_in_module' [''b'']"

lemma get_MT_a:
  fixes M::module
  assumes "has_module_type M MT"
  shows "get_proc_in_module M [''a''] = Some (mk_procedure_untyped (get_MT_a M))"
  using assms unfolding MT_def get_MT_a_def 
  by (rule get_proc_in_module', simp)

lemma get_MT_b:
  fixes M::module
  assumes "has_module_type M MT"
  shows "get_proc_in_module M [''b''] = Some (mk_procedure_untyped (get_MT_b M))"
  using assms unfolding MT_def get_MT_b_def 
  by (rule get_proc_in_module', simp)

(* 
module M : MT = {
  proc a(x:int) { return x>0 }
  proc b(x:int, y:int) { x:=y; return () }
}
*)

abbreviation "x == LVariable ''x'' :: int variable"
abbreviation "y == LVariable ''y'' :: int variable"
definition M_a :: "(int*unit,bool) procedure" where
  "M_a == proc (x) { skip; return x>0 }"
definition M_b :: "(int*int*unit,unit) procedure" where
  "M_b == proc (x,y) { x:=y; return () }"
definition M :: module where
"M == Abs_module \<lparr> mr_module_args=empty,
                   mr_procs=[[''a''] \<mapsto> mk_procedure_untyped M_a,
                             [''b''] \<mapsto> mk_procedure_untyped M_b] \<rparr>"

lemma "has_module_type M MT" sorry

end

