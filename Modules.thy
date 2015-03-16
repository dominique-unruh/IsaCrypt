theory Modules
imports Lang_Typed
keywords "moduletype" :: thy_decl
begin

section {* Module types and modules *}

datatype module_type = ModuleType
 "(id0,module_type) map" (* args *)
 "(id,procedure_type) map" (* procedure types *)
fun mt_proctypes :: "module_type \<Rightarrow> (id,procedure_type) map" where
  "mt_proctypes (ModuleType _ pt) = pt"
fun mt_args :: "module_type \<Rightarrow> (id0,module_type) map" where
  "mt_args (ModuleType a _) = a"

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

definition "ignore x y == y"

definition "has_module_type M == has_module_type' (Rep_module M)"

definition "is_closed_module modul == mr_module_args modul = empty"
fun is_closed_module_type where
 "is_closed_module_type (ModuleType args _) = (args = empty)"


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

(* TODO useful? *)
lemma todo_name:
  fixes modul modulT name
  assumes modtype: "has_module_type' modul modulT"
  assumes proctype: "mt_proctypes modulT name = Some (procedure_type TYPE(('a::procargs,'b::prog_type)procedure))"
  assumes p_def: "mr_procs modul name = Some p"
  assumes closed: "is_closed_module_type modulT"
  shows "mk_procedure_untyped (mk_procedure_typed p::('a,'b)procedure) = p"
proof -
  obtain argT procT where modulT_def: "modulT = ModuleType argT procT" by (cases modulT)
  from proctype have name: "name \<in> dom procT" unfolding modulT_def by auto
  have Abs: "Rep_module (Abs_module modul) = modul"
    apply (rule Abs_module_inverse)
    using modtype unfolding modulT_def by simp
  have type: "has_module_type (Abs_module modul) (ModuleType argT procT)"
    using modtype unfolding has_module_type_def modulT_def Abs .
  with name obtain p' where "get_proc_in_module (Abs_module modul) name = Some p'"
           and wtp': "well_typed_proc' (module_type_map_to_proc_env argT) p'"
           and procT: "Some (proctype_of p') = procT name"
    by (rule module_proc_type, auto)
  with p_def have "p'=p" 
    unfolding get_proc_in_module_def Abs by simp
  from closed have empty: "module_type_map_to_proc_env argT = empty" 
    by (simp add: modulT_def module_type_map_to_proc_env_empty)
  have wtp: "well_typed_proc' empty p"
    using wtp' `p'=p` empty by simp
  obtain body args ret where p_def2: "p=Proc body args ret"
    by (metis wtp option.distinct(1) procedure_rep.exhaust well_typed_proc'.simps(1))
  have body: "well_typed body" using wtp unfolding p_def2 by simp
  have ret: "eu_type ret = Type TYPE('b)"
    using procT proctype unfolding `p'=p` p_def2 modulT_def procedure_type_def by simp
  have args: "args \<in> procargvars TYPE('a)"
    by (metis Abs get_proc_in_module_def has_module_type_def modtype modulT_def module_proc_type mt_proctypes.simps name option.inject p_def p_def2 procedure_type_procargvars proctype)
  from body args ret show "mk_procedure_untyped (mk_procedure_typed p::('a,'b)procedure) = p"
    unfolding p_def2 by (rule mk_procedure_typed_inverse)
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

consts substitute_procs_in_proc :: 'a (* TODO: true thing *)

(* TODO move *)
consts closed_program :: "program_rep \<Rightarrow> bool" (* TODO does not contain ProcRef *)
lemma closed_program_well_typed: "closed_program p \<Longrightarrow> well_typed' E p \<Longrightarrow> well_typed' E' p" sorry

definition "get_proc_in_module' name modul = mk_procedure_typed (the (mr_procs (Rep_module modul) name))"
definition "get_proc_in_module'' name mk_map modul args = mk_procedure_typed 
  (substitute_procs_in_proc (mk_map args) (the (mr_procs (Rep_module modul) name)))"


lemma get_proc_in_module'':
  fixes M::module and mk_map::"'e\<Rightarrow>(id,procedure_rep)map" and procT name
  assumes type: "has_module_type M (ModuleType argsT procT)"
  (* TODO: extra assumptions *)
  assumes procT: "procT name = Some (procedure_type TYPE(('a::procargs,'b::prog_type)procedure))"
  shows "map_option (substitute_procs_in_proc (mk_map args)) (get_proc_in_module M name) =
    Some (mk_procedure_untyped (get_proc_in_module'' name mk_map M args::('a,'b)procedure))"
proof -
  def E == "module_type_map_to_proc_env argsT"
  obtain p where get_proc: "get_proc_in_module M name = Some p"
             and wt_p: "well_typed_proc' E p"
             and procT_name: "Some (proctype_of p) = procT name"
    unfolding E_def using module_proc_type type procT by blast
  hence p_def: "p = the (mr_procs (Rep_module M) name)"
    unfolding get_proc_in_module_def by auto
  have p_type: "proctype_of p = procedure_type TYPE(('a::procargs,'b::prog_type)procedure)"
    by (metis procT_name option.sel procT)
  obtain body pargs ret where
    subst_p: "substitute_procs_in_proc (mk_map args) p = Proc body pargs ret" 
    and subst_p_type: "proctype_of (substitute_procs_in_proc (mk_map args) p) = procedure_type TYPE(('a::procargs,'b::prog_type)procedure)"
    and wt_p: "well_typed_proc' E (substitute_procs_in_proc (mk_map args) p)"
    and closed: "closed_program (substitute_procs_in_proc (mk_map args) p)"
    (* and other stuff *)
  proof (cases p)
  case (Proc body pargs ret)
    thus ?thesis sorry 
  next case (ProcRef body pargs ret)
    thus ?thesis sorry
  qed
  from wt_p have wt_body: "well_typed' E body"
    unfolding subst_p by simp
  have "well_typed body" apply (rule closed_program_well_typed) using closed wt_p apply simp

  show "map_option (substitute_procs_in_proc (mk_map args)) (get_proc_in_module M name) =
         Some (mk_procedure_untyped (get_proc_in_module'' name mk_map M args::('a,'b)procedure))" 
     unfolding get_proc_in_module''_def p_def[symmetric] subst_p
       apply (subst mk_procedure_typed_inverse)
       (* well_typed body *)
       apply (fact wt_body)
       (* pargs \<in> procargvars TYPE('a) *)
       using subst_p_type wt_p unfolding p_def apply (rule procedure_type_procargvars)
    (* eu_type ret = Type TYPE('b) *)
    using p_type apply (simp add: p_def procedure_type_def)
    (* get_proc_in_module M name = Some (Proc body pargs ret) *)
    by (simp add: get_proc p_def)
       sorry
next
case (Proc body pargs ret)
  note proc = this


  show "map_option (substitute_procs_in_proc (mk_map args)) (get_proc_in_module M name) =
       Some (mk_procedure_untyped (get_proc_in_module'' name mk_map M args::('a,'b)procedure))" 
qed


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
    (* well_typed body *)
    using wt_p p_def apply simp
    (* args \<in> procargvars TYPE('a) *)
    using p_type wt_p unfolding p_def apply (rule procedure_type_procargvars)
    (* eu_type ret = Type TYPE('b) *)
    using p_type apply (simp add: p_def procedure_type_def)
    (* get_proc_in_module M name = Some (Proc body args ret) *)
    by (simp add: get_proc p_def)
qed


lemma module_type_nonempty: 
  assumes "finite (dom (mt_proctypes mT))"
  assumes "finite (dom (mt_args mT))"
  shows "\<exists>m. has_module_type m mT"
proof -
  obtain argT procT where mT_def: "mT = ModuleType argT procT" by (cases mT)
  let ?some = "\<lambda>t p. well_typed_proc' (module_type_map_to_proc_env argT) p \<and> proctype_of p = t"
  def procs == "(\<lambda>t. Some (SOME p. ?some t p)) \<circ>\<^sub>m procT"
  have some: "\<And>t. ?some t (SOME p. ?some t p)" 
    by (rule someI_ex, rule proctype_nonempty)
  hence procs_good: "\<And>name t. 
    procT name = Some t \<Longrightarrow> case procs name of None \<Rightarrow> False | Some p \<Rightarrow> proctype_of p = t"
    unfolding procs_def by auto
  def m == "Abs_module \<lparr> mr_module_args=argT, mr_procs=procs \<rparr>"

  have wt_mod: "well_typed_module \<lparr> mr_module_args=argT, mr_procs=procs \<rparr>"
    unfolding well_typed_module_def
    apply (rule, smt2 assms(1) domIff mT_def map_comp_simps(1) module_rep.select_convs(2) mt_proctypes.simps procs_def rev_finite_subset subsetI)
    apply (rule, metis assms(2) mT_def module_rep.select_convs(1) mt_args.simps)
    apply simp
    by (smt2 map_comp_Some_iff mem_Collect_eq option.sel procs_def proctype_nonempty ran_def someI_ex)
    
  hence rep: "Rep_module m = \<lparr> mr_module_args=argT, mr_procs=procs \<rparr>"
    unfolding m_def by (subst Abs_module_inverse, simp_all)
    
  have "has_module_type m mT" 
    unfolding has_module_type_def mT_def apply (simp add: rep wt_mod)
    apply (rule, case_tac "procT name", auto)
    using procs_good by auto
  thus "\<exists>m. has_module_type m mT" ..
qed

ML_file "modules.ML"

section {* Some tests (TODO: remove) *}


moduletype MT where
    a :: "(int*unit,bool) procedure" 
and b :: "(int*int*unit,unit) procedure";

print_theorems

locale bla = fixes bla :: "'a::prog_type" begin
definition "xxx == {undefined bla::int}"

term xxx
thm xxx_def

print_commands

moduletype MTX attach bla where
    a :: "('a*unit,bool) procedure" 
print_theorems

ML "val MT = the (!last_defined_module_type)"
end

typedef MT = "{m. has_module_type m MT}" 
  apply (unfold mem_Collect_eq, rule module_type_nonempty)
  by (simp_all add: MT_def)


text {* 
module M : MT = {
  proc a(x:int) { return x>0 }
  proc b(x:int, y:int) { x:=y; return () }
}
*}


locale M begin
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


(* TODO: make sure that the args of ()procedure are well-sorted.
  Example 

typedecl c
moduletype EncScheme where
    dec :: "('c*unit, unit) procedure"

should give a comprehensible error  
*)


end

