theory Modules2
imports Lang_Typed
begin

class module_type =
  fixes "module_type_procs" :: "'a \<Rightarrow> procedure_rep list"
  fixes "module_type_proc_names" :: "'a itself \<Rightarrow> id list"
  fixes "module_type_proc_types" :: "'a itself \<Rightarrow> procedure_type list"
  assumes "distinct (module_type_proc_names TYPE('a))"
  assumes "length (module_type_procs a) = length (module_type_proc_names TYPE('a))"
  assumes "length (module_type_procs a) = length (module_type_proc_types TYPE('a))"

class module_type_closed = module_type

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
instance
  apply intro_classes
  unfolding module_type_proc_names_MT_def apply simp
  unfolding module_type_procs_MT_def apply simp
  unfolding module_type_proc_types_MT_def apply simp
done
end

abbreviation "typeof (x::'a) == TYPE('a)"

consts subst_proc :: "procedure_rep list \<Rightarrow> procedure_rep \<Rightarrow> procedure_rep"

typedef MT2 = "{p. proctype_of p = procedure_type TYPE((bool*unit,bool)procedure) \<and>
   well_typed_proc' (module_type_proc_types TYPE(MT)) p}" sorry
definition "MT2_b m \<equiv> \<lambda>MT::MT. mk_procedure_typed (subst_proc (module_type_procs MT) (Rep_MT2 m)) :: (bool*unit,bool)procedure"
instantiation MT2 :: module_type begin
definition "module_type_procs_MT2 (m::MT2) == [Rep_MT2 m] :: procedure_rep list" 
definition "module_type_proc_names_MT2 (_::MT2 itself) == [[''b'']]" 
definition "module_type_proc_types_MT2 (_::MT2 itself) == [procedure_type TYPE((bool*unit,bool)procedure)]"
instance apply intro_classes
  unfolding module_type_proc_names_MT2_def module_type_procs_MT2_def module_type_proc_types_MT2_def 
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


