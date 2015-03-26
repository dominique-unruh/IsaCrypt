theory Modules2
imports Lang_Typed
begin

datatype procedure_type_open = ProcTypeOpen "procedure_type_open list" "procedure_type"

class module_type =
  fixes "module_type_procs" :: "'a \<Rightarrow> procedure_rep list"
  fixes "module_type_proc_names" :: "'a itself \<Rightarrow> id list"
  fixes "module_type_proc_types" :: "'a itself \<Rightarrow> procedure_type list"
  fixes "module_type_environment" :: "'a itself \<Rightarrow> procedure_type_open list"
  assumes "distinct (module_type_proc_names TYPE('a))"
  assumes "length (module_type_procs a) = length (module_type_proc_names TYPE('a))"
  assumes "length (module_type_procs a) = length (module_type_proc_types TYPE('a))"

class module_type_closed = module_type +
  assumes "module_type_environment TYPE('a) = []"

(*
datatype parametric_proc_type = ParamProc "parametric_proc_type list"

type_synonym parametric_proc_untyped = "parametric_proc_type * (procedure_rep list \<Rightarrow> procedure_rep)"

inductive parametric_proc :: "parametric_proc_untyped list \<Rightarrow> parametric_proc_untyped \<Rightarrow> bool" where
(* Instantiate environment proc *)
"p \<in> set env \<Longrightarrow> \<forall>p'\<in>set params. parametric_proc env p' \<Longrightarrow> parametric_proc env
(* Apply proc constructors *)
*)

typedef MT = "{p::procedure_rep. proctype_of p = procedure_type TYPE((unit,int)procedure)}" sorry
definition "MT_a m == mk_procedure_typed (Rep_MT m) :: (unit,int)procedure"
instantiation MT :: module_type_closed begin
definition "module_type_procs_MT (m::MT) == [Rep_MT m]"
definition "module_type_proc_names_MT (_::MT itself) == [[''a'']] :: id list"
definition "module_type_proc_types_MT (_::MT itself) == [procedure_type TYPE((unit,int)procedure)]"
definition "module_type_environment_MT (_::MT itself) == []::procedure_type_open list"
instance
  apply intro_classes
  unfolding module_type_environment_MT_def module_type_proc_names_MT_def module_type_procs_MT_def module_type_proc_types_MT_def 
  apply auto
  done
end

abbreviation "typeof (x::'a) == TYPE('a)"

fun nth_opt :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "nth_opt (x#xs) 0 = Some x"
| "nth_opt (x#xs) (Suc n) = nth_opt xs n"
| "nth_opt [] _ = None"


function (sequential) well_typed'' :: "procedure_type_open list \<Rightarrow> program_rep \<Rightarrow> bool" 
and well_typed_proc'' :: "procedure_type_open list \<Rightarrow> procedure_rep \<Rightarrow> bool" where
  "well_typed'' E (Seq p1 p2) = (well_typed'' E p1 \<and> well_typed'' E p2)"
| "well_typed'' E (Assign v e) = (eu_type e = vu_type v)"
| "well_typed'' E (Sample v e) = (ed_type e = vu_type v)"
| "well_typed'' E Skip = True"
| "well_typed'' E (While e p) = ((eu_type e = bool_type) \<and> well_typed'' E p)"
| "well_typed'' E (IfTE e thn els) = ((eu_type e = bool_type) \<and> well_typed'' E thn \<and> well_typed'' E els)"
| "well_typed'' E (CallProc v prc args) =
    (let procT = proctype_of prc in
    vu_type v = pt_returntype procT \<and> 
    list_all2 (\<lambda>e T. eu_type e = T) args (pt_argtypes procT) \<and>
    well_typed_proc'' E prc)"
| "well_typed_proc'' E (ProcRef i env argtypes returntype) = 
    (case nth_opt E i of Some(ProcTypeOpen pi_envT pi_t) \<Rightarrow>
    length pi_envT = length env \<and>
    (\<forall>(T,p)\<in>set (zip pi_envT env). case T of ProcTypeOpen e T \<Rightarrow> (proctype_of p = T 
                        \<and> well_typed_proc'' e p)) \<and>
    pi_t = \<lparr> pt_argtypes=argtypes, pt_returntype=returntype \<rparr>)"
| "well_typed_proc'' E (Proc body pargs ret) = 
    (well_typed'' E body \<and> list_all (\<lambda>v. \<not> vu_global v) pargs \<and> distinct pargs)" by pat_completeness auto

termination apply (relation "measure (\<lambda>x. case x of 
  Inl(E,p) \<Rightarrow> size_list size(E) + size(p)
| Inr(E,p) \<Rightarrow> size_list size(E) + size(p))", auto)
proof -
  fix E e pi_envT::"procedure_type_open list" and p::procedure_rep and
      env::"procedure_rep list"
      and i::nat and pi_T T
  {fix l::"'a::size list" and n and s have "size_option size (nth_opt l n) \<le> size_list size l"
    apply (induction l arbitrary: n, auto)
    apply (case_tac n, auto)
    by (metis le_SucI trans_le_add2)}
  note nth_size = this
  assume ass1: "nth_opt E i = Some (ProcTypeOpen pi_envT pi_T)"
  have "size_option size (Some (ProcTypeOpen pi_envT pi_T)) \<le> size_list size E"
  thm size_option_def
    unfolding ass1[symmetric] by (rule nth_size)
  hence "size (ProcTypeOpen pi_envT pi_T) < size_list size E"
    by auto
  hence size_pi_envT: "size_list size pi_envT < size_list size E" by auto
  assume zip: "(ProcTypeOpen e T, p) \<in> set (zip pi_envT env)"
  hence "ProcTypeOpen e T \<in> set pi_envT"
    by (metis in_set_zipE)
  hence "size (ProcTypeOpen e T) \<le> size_list size pi_envT" apply auto
    by (metis add_Suc_right eq_iff monoid_add_class.add.right_neutral procedure_type_open.size(2) size_list_estimation')
  with size_pi_envT have "size (ProcTypeOpen e T) < size_list size E" by auto
  hence "size_list size e < size_list size E" by auto
  moreover from zip have "p\<in>set env" by (metis in_set_zipE)
  hence "size p \<le> size_list size env"
    by (metis order_refl size_list_estimation') 
  ultimately
  show "size_list size e + size p < Suc (size_list size E + size_list size env)" by auto
qed

(* Termination analysis: 
well_typed'' E p \<longrightarrow> well_typed'' E, subterm(p)
well_typed'' E p \<longrightarrow> well_typed'' E, subterm(p)
well_typed_proc'' E p \<longrightarrow> well_typed'' E subterm(p)
well_typed_proc'' E p \<longrightarrow> well_typed_proc'' subterm(E) subterm(p)
*)


function (sequential) subst_proc_in_prog :: "procedure_rep list \<Rightarrow> program_rep \<Rightarrow> program_rep" 
and subst_proc :: "procedure_rep list \<Rightarrow> procedure_rep \<Rightarrow> procedure_rep" where
  "subst_proc_in_prog env Skip = Skip"
| "subst_proc_in_prog env (Seq c1 c2) = Seq (subst_proc_in_prog env c1) (subst_proc_in_prog env c2)"
| "subst_proc env (Proc body args ret) = Proc (subst_proc_in_prog env body) args ret"
| "subst_proc env (ProcRef i env' argsT retT)
    = subst_proc (map (subst_proc env) env') (env!i)"
by pat_completeness auto

definition "module_type_proc_types_open MT \<equiv> 
  map (ProcTypeOpen (module_type_environment MT)) (module_type_proc_types MT)"

definition "MT2_env \<equiv> module_type_proc_types_open TYPE(MT)"
typedef MT2 = "{procs. length procs = 1 \<and> map proctype_of procs = [procedure_type TYPE((bool*unit,bool)procedure)] \<and>
  (\<forall>p\<in>set procs. well_typed_proc'' MT2_env p)}" sorry
definition "MT2_b m \<equiv> \<lambda>MT::MT. mk_procedure_typed (subst_proc (module_type_procs MT) (Rep_MT2 m!0)) :: (bool*unit,bool)procedure"
instantiation MT2 :: module_type begin
definition "module_type_procs_MT2 (m::MT2) == Rep_MT2 m :: procedure_rep list" 
definition "module_type_proc_names_MT2 (_::MT2 itself) == [[''b'']]" 
definition "module_type_proc_types_MT2 (_::MT2 itself) == [procedure_type TYPE((bool*unit,bool)procedure)]"
definition "module_type_environment_MT2 (_::MT2 itself) == MT2_env"
instance apply intro_classes
  unfolding module_type_proc_names_MT2_def module_type_procs_MT2_def module_type_proc_types_MT2_def 
  using Rep_MT2
  by auto
end

typedef MT3 = "{(x,y).
  proctype_of x=procedure_type TYPE((bool*unit,string)procedure) \<and>
  proctype_of y=procedure_type TYPE((string*unit,string)procedure) \<and>
  well_typed_proc' (module_type_proc_types TYPE(MT) @ module_type_proc_types TYPE(MT2)) x \<and>
  well_typed_proc' (module_type_proc_types TYPE(MT) @ module_type_proc_types TYPE(MT2)) y}" sorry
definition "MT3_x (m::MT3) (m1::MT) (m2::MT2) \<equiv>
  case Rep_MT3 m of (x,y) \<Rightarrow> (mk_procedure_typed (subst_proc (module_type_procs m1 @ module_type_procs m2) x) :: (bool*unit,string)procedure)"
definition "MT3_y (m::MT3) (m1::MT) (m2::MT2) \<equiv>
  case Rep_MT3 m of (x,y) \<Rightarrow> (mk_procedure_typed (subst_proc (module_type_procs m1 @ module_type_procs m2) y) :: (string*unit,string)procedure)"
instantiation MT3 :: module_type begin
definition "module_type_procs_MT3 (m::MT3) == case Rep_MT3 m of (x,y) \<Rightarrow> [x,y]" 
definition "module_type_proc_names_MT3 (_::MT3 itself) == [[''x''],[''y'']]" 
definition "module_type_proc_types_MT3 (_::MT3 itself) == [procedure_type TYPE((bool*unit,string)procedure), procedure_type TYPE((string*unit,string)procedure)]" 
instance apply intro_classes sorry
end


