theory Modules
imports Lang_Typed
keywords "moduletype" :: thy_decl
begin

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


section {* Some tests (TODO: remove) *}
  
text {*
module type MT = {
  proc a(int) : bool
  proc b(int,int) : unit
}
*}

ML {*
  type module_type_spec_raw = 
  { mt_name: binding,
    mt_args: (binding*string) list,
    mt_proctypes: (binding*string) list
  };
  type module_type_spec = 
  { mt_name: binding,
    mt_args: (string*term) list,
    mt_proctypes: (binding*string list*typ) list,
    mt_def_thm : thm option,
    mt_getter_def_thms : (binding*string list*thm) list
  };
*}

ML {* @{term "procedure_type TYPE((unit,unit)procedure)"} *}

ML {*
  fun mk_id n = HOLogic.mk_list @{typ string} (map HOLogic.mk_string n)

  local
  fun optionT t = Type(@{type_name option},[t]);
  fun Some x = let val t = fastype_of x in Const(@{const_name Some},t --> optionT t) $ x end

  fun fun_upd f x y = 
    let val tx = fastype_of x
        val ty = fastype_of y 
    in
    Const(@{const_name fun_upd}, (tx --> ty) --> tx --> ty --> (tx --> ty)) $ f $ x $ y
    end                   

  fun empty_map t1 t2 = Abs ("x", t1, Const (@{const_name None}, optionT t2))
  in
  fun alist_to_HOL_map t1 t2 l = fold (fn (x,y) => fn m => 
    fun_upd m x (Some y)) l (empty_map t1 t2);
  end;

  local
  fun procedure_type pt =
    Const (@{const_name procedure_type}, Term.itselfT pt --> @{typ procedure_type}) $
       Const(@{const_name Pure.type}, Term.itselfT pt);
  
  in
  fun mk_module_type (spec:module_type_spec) =
  (* TODO: check if names unique *)
  let val args = alist_to_HOL_map @{typ string} @{typ module_type}
                 (map (fn (n,mt) => (HOLogic.mk_string n,mt)) (#mt_args spec))
      val procT = #mt_proctypes spec |>
                  map (fn (_,n,pt) => (mk_id n, procedure_type pt)) |>
                  alist_to_HOL_map @{typ "string list"} @{typ procedure_type}
  in
    @{term ModuleType} $ args $ procT
  end 
  end
*}

(* definition MT :: module_type where
"MT == ModuleType empty [[''a''] \<mapsto> procedure_type TYPE((int*unit,bool)procedure),
                         [''b''] \<mapsto> procedure_type TYPE((int*int*unit,unit)procedure)]"
*)

ML {*
  fun update_mt_def_thm ({mt_name,mt_args,mt_proctypes,mt_def_thm=_,mt_getter_def_thms}:module_type_spec) mt_def_thm =
     {mt_name=mt_name,mt_args=mt_args,mt_proctypes=mt_proctypes,mt_def_thm=mt_def_thm,mt_getter_def_thms=mt_getter_def_thms}
  fun update_mt_getter_def_thms ({mt_name,mt_args,mt_proctypes,mt_def_thm,mt_getter_def_thms=_}:module_type_spec) mt_getter_def_thms =
     {mt_name=mt_name,mt_args=mt_args,mt_proctypes=mt_proctypes,mt_def_thm=mt_def_thm,mt_getter_def_thms=mt_getter_def_thms}

*}

print_commands


ML {*
(*  val parse_multipart_string =
    Parse.binding >> (fn bind => Binding.name_of bind |> Long_Name.explode); *)

  fun read_term_T ctx T term = Syntax.parse_term ctx term 
                               |> Type.constraint T
                               |> Syntax.check_term ctx

  val parse_module_subtyping = Parse.$$$ ":" || (Parse.$$$ "<" --| Parse.$$$ ":")

  (* Parses (A<:MT1,B<:MT2,...)  --or A:MT1 etc*)
  val parse_module_type_args : (binding*string) list parser = 
    Parse.$$$ "(" |-- Parse.!!! (Parse.enum "," (Parse.binding --| parse_module_subtyping -- Parse.term)) --| Parse.$$$ ")"

  (* Parses "name(A<:MT1,B<:MT2,...) where a :: type" *)
  val parse_module_type : module_type_spec_raw parser = 
    Parse.binding -- (* moduletype MT *) 
    Scan.optional parse_module_type_args [] --| 
    @{keyword "where"} -- (Parse.and_list (Parse.binding --| Parse.$$$ "::" -- Parse.typ))
    >> (fn ((name,args),procs) => { mt_name=name, mt_proctypes=procs, mt_args=args });

  fun module_type_spec_process 
      ({mt_name=name, mt_args=args, mt_proctypes=procs}:module_type_spec_raw) 
      lthy : module_type_spec =
  {mt_name=name, 
   mt_args=map (fn (n,t) => (Binding.name_of n,read_term_T lthy @{typ module_type} t)) args,
   mt_proctypes=map (fn (n,t) => (n,Long_Name.explode (Binding.name_of n), Syntax.read_typ lthy t)) procs,
   mt_def_thm=NONE, mt_getter_def_thms=[]
  }
*}

ML {*
val last_defined_module_type = Unsynchronized.ref NONE

(* definition get_MT_a :: "module \<Rightarrow> (int*unit,bool) procedure" where
  "get_MT_a = get_proc_in_module' [''a'']" *)

(* TODO: Should replace . by _ in getter_name *)
fun define_module_type_getter (name_bind, name:string list, procT) 
                              (lthy, mt:module_type_spec) : (local_theory*module_type_spec)=
  let val getter_name = Binding.name ("get_"^(Binding.name_of(#mt_name mt))^"_"^String.concatWith "_" name)
      val getter_def = Const(@{const_name get_proc_in_module'},@{typ id} --> @{typ module} --> procT)
                       $ mk_id name
      val ((_,(_,thm)),lthy) = Local_Theory.define ((getter_name, NoSyn),
          ((Thm.def_binding getter_name,[]), getter_def)) lthy
      val mt : module_type_spec = update_mt_getter_def_thms mt ((name_bind,name,thm) :: #mt_getter_def_thms mt)
  in (lthy,mt) end

fun define_module_type (spec_raw:module_type_spec_raw) lthy =
  let val mt = module_type_spec_process spec_raw lthy
      val ((_,(_,thm)),lthy) = Local_Theory.define ((#mt_name mt, NoSyn), 
                           ((Thm.def_binding (#mt_name mt),[]), mk_module_type mt)) lthy 
      val mt : module_type_spec = update_mt_def_thm mt (SOME thm)
      val (lthy,mt) = if (#mt_args mt=[]) 
                      then fold define_module_type_getter (#mt_proctypes mt) (lthy,mt) 
                      else (lthy,mt)
      val _ = (last_defined_module_type := SOME mt)
  in
  lthy
  end
*}

ML {*
  Outer_Syntax.local_theory @{command_spec "moduletype"} "Declares a module type"
    (parse_module_type >> define_module_type)
*}

moduletype MT where
    a :: "(int*unit,bool) procedure" 
and b :: "(int*int*unit,unit) procedure";

print_theorems

ML "the (!last_defined_module_type)"

typedef MT = "{m. has_module_type m MT}"
  apply (unfold mem_Collect_eq, rule module_type_nonempty)
  by (simp_all add: MT_def)

lemma get_MT_a:
  "has_module_type M MT \<Longrightarrow> get_proc_in_module M [''a''] = Some (mk_procedure_untyped (get_MT_a M))"
  unfolding get_MT_a_def 
  apply (rule get_proc_in_module')
  unfolding MT_def
  apply (fact asm_rl)
  apply simp
done

lemma get_MT_b:
  fixes M::module
  assumes "has_module_type M MT"
  shows "get_proc_in_module M [''b''] = Some (mk_procedure_untyped (get_MT_b M))"
  using assms unfolding MT_def get_MT_b_def 
  by (rule get_proc_in_module', simp)

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

term "M.x"

end

