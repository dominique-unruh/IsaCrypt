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

definition module_type_proc_env :: "module_type \<Rightarrow> (id,procedure_type)map" where
  "module_type_proc_env mt = module_type_map_to_proc_env (mt_args mt)"

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

(* TODO move *)
fun substitute_procs :: "(id,procedure_rep)map \<Rightarrow> program_rep \<Rightarrow> program_rep" where
  "substitute_procs m Skip = Skip"
fun substitute_procs_in_proc :: "(id,procedure_rep)map \<Rightarrow> procedure_rep \<Rightarrow> procedure_rep" where
  "substitute_procs_in_proc m (Proc body args ret) = Proc (substitute_procs m body) args ret"
| "substitute_procs_in_proc m (ProcRef name args ret) = the (m name)"

(* TODO move *)
lemma substitute_procs_in_proc_welltyped:
  assumes "well_typed_proc' ((map_option proctype_of) o m) p"
  assumes "\<forall>p'\<in>ran(m). well_typed_proc' empty p'"
  shows "well_typed_proc' empty (substitute_procs_in_proc m p)"
sorry


(* TODO move *)
lemma substitute_procs_in_proc_type:
  assumes "well_typed_proc' ((map_option proctype_of) o m) p"
  shows "proctype_of (substitute_procs_in_proc m p) = proctype_of p"
proof (cases p)
case (Proc body args ret)
  thus ?thesis by simp
next case (ProcRef name argsT retT)
  note p = this
  with assms obtain p' where p': "m name = Some p'"
    and p'_type: "proctype_of p' = \<lparr>pt_argtypes = argsT, pt_returntype = retT\<rparr>"
    by auto
  show ?thesis 
    by (simp add: p p' p'_type)
qed
(* TODO move *)
(* closed_program p \<equiv> p does not contain ProcRef's *)
fun closed_program :: "program_rep \<Rightarrow> bool" where
  "closed_program Skip = True"
| "closed_program (Assign v e) = True"
| "closed_program (Sample v e) = True"
| "closed_program (Seq c d) = (closed_program c \<and> closed_program d)"
| "closed_program (CallProc v (Proc body args ret) a) = closed_program body"
| "closed_program (CallProc v (ProcRef name argsT retT) a) = False"
| "closed_program (While e p) = closed_program p"
| "closed_program (IfTE e p1 p2) = (closed_program p1 \<and> closed_program p2)"
print_theorems

(* TODO move *)
lemma closed_program_well_typed: "closed_program p \<Longrightarrow> well_typed' E p \<Longrightarrow> well_typed' E' p"
  by (induction rule: closed_program.induct, auto)

(* TODO move *)
lemma well_typed_proc_closed: 
  assumes "well_typed_proc' empty (Proc body args ret)"
  shows "closed_program body"
proof -
  from assms have "well_typed body" by auto
  thus "closed_program body"
    by (induction rule: closed_program.induct, simp_all)
qed


definition "get_proc_in_module' name modul = mk_procedure_typed (the (mr_procs (Rep_module modul) name))"
definition "get_proc_in_module'' name mk_map modul args = mk_procedure_typed 
  (substitute_procs_in_proc (mk_map args) (the (mr_procs (Rep_module modul) name)))"


lemma get_proc_in_module'':
  fixes M::module and mk_map::"'e\<Rightarrow>(id,procedure_rep)map" and procT name
  assumes type: "has_module_type M (ModuleType argsT procT)"
  assumes mk_map_t: "map_option proctype_of \<circ> mk_map args = module_type_proc_env (ModuleType argsT procT)"
  assumes wt_mk_map: "\<forall>p'\<in>ran (mk_map args). well_typed_proc' Map.empty p'"
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

  have subst_p_type: "proctype_of (substitute_procs_in_proc (mk_map args) p) = procedure_type TYPE(('a::procargs,'b::prog_type)procedure)"
    apply (fold p_type, rule substitute_procs_in_proc_type)
    by (metis E_def mk_map_t module_type_proc_env_def mt_args.simps wt_p)

  have wt_subst_p: "well_typed_proc' empty (substitute_procs_in_proc (mk_map args) p)"
    apply (rule substitute_procs_in_proc_welltyped)
    apply (metis E_def mk_map_t module_type_proc_env_def mt_args.simps wt_p)
    by (fact wt_mk_map)

  obtain body pargs ret where
    subst_p: "substitute_procs_in_proc (mk_map args) p = Proc body pargs ret" 
  proof (cases p)
  case (Proc body' pargs ret)
    note p = this
    def body == "substitute_procs (mk_map args) body'"
    have subst_p: "substitute_procs_in_proc (mk_map args) p = Proc body pargs ret"
      unfolding p body_def by simp
    with that show ?thesis by auto
  next case (ProcRef name pargsT retT)
    note p = this
    obtain p' where p': "mk_map args name = Some p'"
    proof -
      from mk_map_t have "(map_option proctype_of \<circ> mk_map args) name = module_type_proc_env (ModuleType argsT procT) name"
        by simp
      hence none: "mk_map args name = None \<Longrightarrow> module_type_proc_env (ModuleType argsT procT) name = None"
        by simp
      have "module_type_proc_env (ModuleType argsT procT) name \<noteq> None"
        using wt_p by (simp add: p E_def module_type_proc_env_def)
      with none and that show ?thesis by auto
    qed
    obtain body args' ret where "p' = Proc body args' ret"
    proof (cases p')
    case (Proc body args' ret) with that show ?thesis by auto
    next case (ProcRef name argsT retT)
      note thecase = this
      from p' have "p'\<in>ran (mk_map args)" by (rule ranI)
      with wt_mk_map have "well_typed_proc' Map.empty p'" by simp
      thus ?thesis unfolding thecase by auto
    qed
    hence subst_p: "substitute_procs_in_proc (mk_map args) p = Proc body args' ret"
      by (simp add: p p')
    with that show ?thesis by auto
  qed
  from wt_subst_p have wt_body: "well_typed' empty body"
    unfolding subst_p by simp
  have closed: "closed_program body"
    apply (rule well_typed_proc_closed[where args=pargs and ret=ret])
    apply (fold subst_p)
    by (fact wt_subst_p)

  show "map_option (substitute_procs_in_proc (mk_map args)) (get_proc_in_module M name) =
         Some (mk_procedure_untyped (get_proc_in_module'' name mk_map M args::('a,'b)procedure))" 
     unfolding get_proc_in_module''_def p_def[symmetric] subst_p
       apply (subst mk_procedure_typed_inverse)
       (* well_typed body *)
       apply (rule closed_program_well_typed, fact closed, fact wt_body)
       (* pargs \<in> procargvars TYPE('a) *)
       using subst_p_type[unfolded subst_p] wt_subst_p[unfolded subst_p] 
       unfolding p_def apply (rule procedure_type_procargvars)
       (* eu_type ret = Type TYPE('b) *)
       using subst_p_type subst_p apply (simp add: p_def procedure_type_def)
       (* get_proc_in_module M name = Some (Proc body pargs ret) *)
       apply simp by (metis get_proc subst_p)
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
  a :: "(unit,int) procedure";
print_theorems
moduletype MT2(M:MT) where
  b :: "(unit,unit) procedure";
print_theorems
definition MT2_b :: "module \<Rightarrow> (unit,int)procedure \<Rightarrow> (unit,unit)procedure" where
  "MT2_b \<equiv> get_proc_in_module'' [''b''] (\<lambda>a. [[''a'']\<mapsto>mk_procedure_untyped a])"

(* TODO move *)
lemma proctype_mk_untyped [simp]:
  "proctype_of (mk_procedure_untyped (p::('a::procargs,'b::prog_type)procedure))
  = procedure_type TYPE(('a,'b)procedure)"
sorry

lemma MT2_b:
  fixes M and a::"(unit,int)procedure"
  assumes type:"has_module_type M MT2"
  shows "map_option (substitute_procs_in_proc [[''a'']\<mapsto>mk_procedure_untyped a]) (get_proc_in_module M [''b'']) =
       Some (mk_procedure_untyped (MT2_b M a))"
proof (unfold MT2_b_def, rule get_proc_in_module'')
  def argsT == "[''M'' \<mapsto> MT]" and procT == "[[''b''] \<mapsto> procedure_type TYPE((unit, unit) procedure)]"
  def mk_map == "\<lambda>a::(unit,int)procedure. [[''a'']\<mapsto>mk_procedure_untyped a]"
  have MT2_def: "MT2 == ModuleType argsT procT" unfolding MT2_def argsT_def procT_def.
  show "has_module_type M (ModuleType argsT procT)" by (fold MT2_def, fact type)
  show "map_option proctype_of \<circ> (mk_map a) = module_type_proc_env (ModuleType argsT procT)"
    unfolding mk_map_def argsT_def procT_def apply simp
    unfolding module_type_proc_env_def MT_def apply simp
    apply (rule ext, case_tac x, simp, simp)
    sorry
  show "\<forall>p'\<in>ran (mk_map a). well_typed_proc' Map.empty p'" sorry
  show "procT [''b''] = Some (procedure_type TYPE((unit,unit) procedure))" sorry
qed

abbreviation "xxx == Variable ''x'' :: int variable"
definition "mt2_b (a::(unit,int)procedure) \<equiv>
  proc() { xxx:=call a(); xxx:=call a(); return () }"

ML {* @{thm mt2_b_def} *}

definition "parametric_proc E mk_map (p::'e\<Rightarrow>('a::procargs,'b::prog_type)procedure) ==
   SOME p'. proctype_of p' = procedure_type TYPE(('a,'b)procedure) \<and> well_typed_proc' E p' \<and>
   (\<forall>a. mk_procedure_untyped (p a) = substitute_procs_in_proc (mk_map a) p')"
print_theorems

definition "parametric_proc_exists E mk_map (p::'e\<Rightarrow>('a::procargs,'b::prog_type)procedure) == 
   \<exists>p'. proctype_of p' = procedure_type TYPE(('a,'b)procedure) \<and> well_typed_proc' E p' \<and>
   (\<forall>a. mk_procedure_untyped (p a) = substitute_procs_in_proc (mk_map a) p')"

lemma parametric_proc_props:
  assumes ex:"parametric_proc_exists E mk_map (p::'e\<Rightarrow>('a::procargs,'b::prog_type)procedure)"
  defines "p' \<equiv> parametric_proc E mk_map p"
  shows "proctype_of p' = procedure_type TYPE(('a,'b)procedure)" 
  and   "well_typed_proc' E p'"
  and   "\<And>a. mk_procedure_untyped (p a) = substitute_procs_in_proc (mk_map a) p'"
using someI_ex[OF ex[unfolded parametric_proc_exists_def]]
unfolding p'_def parametric_proc_def by metis+

definition "parametric_prog_exists E mk_map p == 
   \<exists>p'. well_typed' E p' \<and>
   (\<forall>a. mk_program_untyped (p a) = substitute_procs (mk_map a) p')"

lemma parametric_proc_exists_proc:
  fixes (* pbody :: "'e \<Rightarrow> program" and args::"'a::procargs procargvars" and ret::"'b::prog_type expression"
    and *) P :: "'e \<Rightarrow> ('a::procargs,'b::prog_type) procedure" and E::"(id,procedure_type) map"
    and mk_map :: "'e \<Rightarrow> (id,procedure_rep) map"
(*  defines "procT == procedure_type TYPE(('a,'b)procedure)" *)
(*  defines "P == \<lambda>a. \<lparr> p_body=pbody a, p_args=args, p_return=ret \<rparr> :: ('a,'b)procedure" *)
  assumes "parametric_prog_exists E mk_map (\<lambda>a. p_body (P a))"
(*  shows "\<exists>p. proctype_of p = procT \<and> well_typed_proc' E p \<and>
    (\<forall>a::'e. mk_procedure_untyped (P a) = substitute_procs_in_proc (mk_map a) p)"*)
  shows "parametric_proc_exists E mk_map P"

sorry


lemma parametric_prog_exists_seq:
  assumes "parametric_prog_exists E mk_map p1"
  assumes "parametric_prog_exists E mk_map p2"
  shows "parametric_prog_exists E mk_map (\<lambda>a. seq (p1 a) (p2 a))"
sorry

lemma parametric_prog_exists_callproc:
  assumes "parametric_proc_exists E mk_map p"
  shows "parametric_prog_exists E mk_map (\<lambda>a. callproc v (p a) args)"
sorry

lemma parametric_proc_exists_ref: (* TODO: generalize to tuples a *)
  assumes "E name = Some \<lparr>pt_argtypes = procargtypes TYPE('a::procargs), pt_returntype = Type TYPE('b::prog_type)\<rparr>"
  assumes "\<And>a. mk_map a name = Some (mk_procedure_untyped a)"
  shows "parametric_proc_exists E mk_map (\<lambda>a. a :: ('a,'b)procedure)"
unfolding parametric_proc_exists_def procedure_type_def
apply (rule_tac x="ProcRef name ?arg ?ret" in exI)
using assms by auto

lemmas parametric_prog_existsI = parametric_prog_exists_callproc parametric_prog_exists_seq
  parametric_proc_exists_proc (* Doesn't automate well: parametric_proc_exists_ref *)

lemma
  defines "E == module_type_proc_env MT2"
  defines "mk_map a == ([[''M'',''a'']\<mapsto>mk_procedure_untyped a])"
  defines "p' == parametric_proc E mk_map mt2_b"
(*  shows "proctype_of p' = procedure_type TYPE((unit,int)procedure)" 
  and   "well_typed_proc' E p'" *)
  shows   "\<And>a. mk_procedure_untyped (mt2_b a) = substitute_procs_in_proc (mk_map a) p'"
unfolding p'_def 
apply (rule parametric_proc_props)
  unfolding mt2_b_def 
  unfolding E_def MT2_def module_type_proc_env_def MT_def procedure_type_def mk_map_def 
  apply (rule parametric_prog_existsI, simp)
  apply (rule parametric_prog_existsI, simp?)
  apply (rule parametric_prog_existsI, simp?)
  apply (rule parametric_proc_exists_ref[where name="[''M'',''a'']"], (auto)[2])
  apply (rule parametric_prog_existsI, simp?)
  apply (rule parametric_proc_exists_ref[where name="[''M'',''a'']"], (auto)[2])
done

lemma mt2_b_good:
  defines "E == module_type_proc_env MT2"
  defines "mk_map a == ([[''M'',''a'']\<mapsto>mk_procedure_untyped a])"
(*  shows "\<exists>p. proctype_of p = procedure_type TYPE((unit,unit)procedure) \<and> well_typed_proc' E p \<and>
    (\<forall>a::(unit,int)procedure. mk_procedure_untyped (mt2_b a) = substitute_procs_in_proc (mk_map a) p)" 
  unfolding parametric_proc_exists_def[symmetric] *)
  shows "parametric_proc_exists E mk_map mt2_b" 
unfolding E_def MT2_def module_type_proc_env_def MT_def procedure_type_def mk_map_def[cong] mt2_b_def[cong] 
  apply (rule parametric_prog_existsI, simp)
  apply (rule parametric_prog_existsI, simp?)
  apply (rule parametric_prog_existsI, simp?)
  apply (rule parametric_proc_exists_ref[where name="[''M'',''a'']"], (auto)[2])
  apply (rule parametric_prog_existsI, simp?)
  apply (rule parametric_proc_exists_ref[where name="[''M'',''a'']"], (auto)[2])
done

definition M2 :: module where
"M2 ==
let E = (module_type_proc_env MT2) in
let mk_map = (\<lambda>a. [[''M'',''a'']\<mapsto>mk_procedure_untyped a]) in
 Abs_module \<lparr> mr_module_args=[''M''\<mapsto>MT],
              mr_procs=[[''b''] \<mapsto> parametric_proc E mk_map
                                         mt2_b ] \<rparr>"

(* MT2.a should exist an be a function "procedure \<Rightarrow> procedure" *)

lemma "has_module_type M2 MT2"
proof - 
  have eq: "module_type_map_to_proc_env [''M'' \<mapsto> MT] = module_type_proc_env MT2"
    unfolding MT2_def module_type_proc_env_def by simp
  have wt_M2: "well_typed_module
     \<lparr>mr_module_args = [''M'' \<mapsto> MT],
        mr_procs =
          [[''b''] \<mapsto>
           parametric_proc (module_type_proc_env MT2)
            (\<lambda>a\<Colon>(unit, int) procedure.
                [[''M'', ''a''] \<mapsto> mk_procedure_untyped a])
            mt2_b]\<rparr>"
    unfolding well_typed_module_def 
    apply auto unfolding eq
    apply (rule parametric_proc_props)
    apply (rule mt2_b_good) done
  show "has_module_type M2 MT2"
    unfolding has_module_type_def
    unfolding M2_def apply simp
    apply (subst Abs_module_inverse, simp)
    apply (rule wt_M2)
    apply (subst (2) MT2_def) apply auto
    apply (rule wt_M2)
    apply (rule parametric_proc_props)
    by (rule mt2_b_good)    
qed
  


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

