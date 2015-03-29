theory Modules
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

thm module_type_class_def

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

ML {*
type module_type_spec = {
  name: binding,
  arguments: {name:binding, typ:typ} list,
  procs: {name:binding, typ:typ} list
};
*}

definition "module_type_rep_set env proctypes \<equiv>
{procs. map proctype_of procs = proctypes \<and> (\<forall>p\<in>set procs. well_typed_proc'' env p)}"
lemma module_type_rep_set_inhabited: "\<exists>x. x \<in> module_type_rep_set env procT"
  sorry

ML {*
fun mk_nat i = 
  if i=0 then @{term "0::nat"}
  else if i<0 then raise Match
  else @{term "Suc"} $ mk_nat (i-1);;
*}

ML {*
val MT2_spec:module_type_spec = {
  name = @{binding MT2},
  procs = [{name = @{binding b}, typ = @{typ "(bool*unit,bool)procedure"}}],
  arguments = [{name = @{binding M}, typ = @{typ "MT"}}] 
};
*}

ML {* @{term "E!1"} *}

ML {*
fun define_module_type (spec:module_type_spec) (thy:theory) =
  let 
      (* Sanity checks on spec *)
      val _ = if has_duplicates (op=) (#arguments spec |> map #name |> map Binding.name_of)
              then raise (ERROR "Two module arguments with the same name")
              else ()
      val _ = if has_duplicates (op=) (#procs spec |> map #name |> map Binding.name_of)
              then raise (ERROR "Two procedures with the same name")
              else ()

      (* Perform the equivalent of:
         typedef MT = "module_type_rep_set 
           (module_type_proc_types_open TYPE(arg1) @ ... @ module_type_proc_types_open TYPE(argn))
           [procedure_type TYPE(proctype1), ... , procedure_type TYPE(proctypen)]"
              by (fact module_type_rep_set_inhabited)
      *)
      val env = #arguments spec
                |> map (fn {typ,...} => 
                   Const(@{const_name module_type_proc_types_open},Term.itselfT typ--> @{typ "procedure_type_open list"})
                           $ Logic.mk_type typ)
                |> foldr1 (fn(x,y) => @{term "append::_\<Rightarrow>_\<Rightarrow>procedure_type_open list"}$x$y)
                   handle List.Empty => @{term "[]::procedure_type_open list"}
      val procTs = #procs spec
                   |> map (fn {typ,...} => Const(@{const_name procedure_type},Term.itselfT typ--> @{typ procedure_type}) $
                                           Logic.mk_type typ)
                   |> HOLogic.mk_list @{typ "procedure_type"}
      val rep_set = @{term module_type_rep_set} $ env $ procTs
      val ((mt_name,typdef_info),thy) = 
        Typedef.add_typedef_global (#name spec,[],NoSyn) rep_set NONE 
            (rtac @{thm module_type_rep_set_inhabited} 1) thy
      val _ = writeln ("Define typed "^mt_name)

      (* Perform equivalent of:
         instantiation MT :: module_type begin *)
      val thy = Class.instantiation ([mt_name],[],@{sort "module_type"}) thy

      (* definition "module_type_procs_MT == Rep_MT" *)
      val bind = #name spec |> Binding.prefix_name "module_type_procs_"
      val MT = #abs_type (fst typdef_info)
      val Rep_MT = let val i=fst typdef_info in Const(#Rep_name i,MT --> #rep_type i) end
      val ((mt_procs_const,(_,mt_procs_def)),thy) = Local_Theory.define
          ((bind,NoSyn), ((Thm.def_binding bind,[]), Rep_MT)) thy

      (* definition "module_type_proc_names_MT == %(_::MT itself). [[''b'']]" *)
      val bind = #name spec |> Binding.prefix_name "module_type_proc_names_"
      val rhs = #procs spec |> map (fn p => #name p |> Binding.name_of 
                  |> Long_Name.explode |> map HOLogic.mk_string
                  |> HOLogic.mk_list @{typ id0}) |> HOLogic.mk_list @{typ id}
                  |> Term.absdummy (Term.itselfT MT)
      val ((mt_proc_names_const,(_,mt_proc_names_def)),thy) = Local_Theory.define
          ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) thy

      (* definition "module_type_proc_types_MT == %(_::MT itself). [procedure_type TYPE((...)procedure)]" *)
      val bind = #name spec |> Binding.prefix_name "module_type_proc_types_"
      val rhs = #procs spec |> map #typ |> map (fn t =>  
                  Const(@{const_name procedure_type},Term.itselfT t--> @{typ procedure_type}) $
                      Logic.mk_type t)
                  |> HOLogic.mk_list @{typ procedure_type}
                  |> Term.absdummy (Term.itselfT MT)
      val ((mt_proc_types_const,(_,mt_proc_types_def)),thy) = Local_Theory.define
          ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) thy

      (* definition "module_type_environment_MT == %(_::MT itself). module_type_proc_types_open TYPE(MT1) @ ..." *)
      val bind = #name spec |> Binding.prefix_name "module_type_environment_"
      val rhs = env |> Term.absdummy (Term.itselfT MT)
      val ((mt_environment_const,(_,mt_environment_def)),thy) = Local_Theory.define
          ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) thy
      
      (* Perform the equivalent of:
         instance sorry *)
      val thy = Class.prove_instantiation_exit (fn _ => Skip_Proof.cheat_tac 1) thy
      (* TODO: Actually prove this *)

      (* Perform equivalent of:
         instantiation MT :: module_type_closed begin
         (if MT is a closed module type)   *)
      val thy = if #arguments spec=[] then
          Class.instantiation ([mt_name],[],@{sort "module_type_closed"}) thy
          |> Class.prove_instantiation_exit (fn _ => Skip_Proof.cheat_tac 1)
          else thy
          (* TODO prove this *)

      (* For each proci in #procs spec: 
         definition "MT.proci == %(M::MT) (M1::arg1) ... (Mn::argn).
                     (mk_procedure_typed (subst_proc
                         (module_type_procs M1 @ ... @ module_type_procs Mn)
                         ((module_type_procs M)!i)) :: (...)procedure)" *)
      val env_procs = #arguments spec
                |> map (fn {typ,name} => 
                   Const(@{const_name module_type_procs},typ--> @{typ "procedure_rep list"})
                           $ Free(Binding.name_of name,typ))
                |> foldr1 (fn(x,y) => @{term "append::_\<Rightarrow>_\<Rightarrow>procedure_rep list"}$x$y)
                   handle List.Empty => @{term "[]::procedure_rep list"}
      val env_proc_vars = #arguments spec
                |> map (fn {typ,name} => (Binding.name_of name,typ))
      val M = Name.variant_list (#arguments spec |> map #name |> map Binding.name_of) [#name spec |> Binding.name_of] |> hd
      fun define_getter (i,proc) (getters,thy:local_theory) =
      let val get_proc = @{term "nth::_\<Rightarrow>_\<Rightarrow>procedure_rep"} $ (Const(@{const_name module_type_procs},MT--> @{typ "procedure_rep list"}) $ Free(M,MT)) $ mk_nat i
          val rhs = Const(@{const_name mk_procedure_typed},@{typ procedure_rep}--> #typ proc) $
                    (@{term subst_proc} $ env_procs $ get_proc)
          val rhs = rhs |> fold absfree (rev env_proc_vars) |> absfree (M,MT)
          val bind = #name proc |> Binding.qualify true (#name spec |> Binding.name_of)
          val ((getter_const,(_,getter_def)),thy) = Local_Theory.define
              ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) thy
      in ((getter_const,getter_def)::getters,thy) end
      val thy = Named_Target.theory_init thy
      val (getters,thy) = fold_index define_getter (#procs spec) ([],thy)
      val thy = Named_Target.exit thy

      val _ = (getters,mt_environment_const,mt_environment_def,mt_proc_types_const,mt_proc_types_def,mt_proc_names_const,mt_proc_names_def, mt_procs_def, mt_procs_const)
  in
  thy
  end;
*}

setup "define_module_type MT2_spec"
thm MT2.b_def






print_theorems





(*definition "module_type_getter i m == mk_procedure_typed (subst_proc (module_type_procs MT) (Rep_MT2 m!i))"*)

(*typedef MT2 = "module_type_rep_set (module_type_proc_types_open TYPE(MT)) [procedure_type TYPE((bool*unit,bool)procedure)]" 
  by (fact module_type_rep_set_inhabited)*)
(*instantiation MT2 :: module_type begin*)
(*definition "module_type_procs_MT2 (m::MT2) == Rep_MT2 m :: procedure_rep list"  *)
(*definition "module_type_proc_names_MT2 (_::MT2 itself) == [[''b'']]" *)
(*definition "module_type_proc_types_MT2 (_::MT2 itself) == [procedure_type TYPE((bool*unit,bool)procedure)]"
definition "module_type_environment_MT2 (_::MT2 itself) == module_type_proc_types_open TYPE(MT)"*)
definition "MT2_b m \<equiv> \<lambda>MT::MT. mk_procedure_typed (subst_proc (module_type_procs MT) (Rep_MT2 m!0)) :: (bool*unit,bool)procedure"

lemma "MT2_b = MT2.b"
  apply (rule ext)
  unfolding MT2_b_def MT2.b_def
  unfolding module_type_procs_MT2_def
  ..
  

ML {*
val MT3_spec:module_type_spec = {
  name = @{binding MT3},
  procs = [{name = @{binding x}, typ = @{typ "(bool*unit,string)procedure"}},
           {name = @{binding y}, typ = @{typ "(string*unit,string)procedure"}}],
  arguments = [{name = @{binding M}, typ = @{typ "MT"}},
               {name = @{binding M2}, typ = @{typ "MT2"}}] 
     };
*}

setup "define_module_type MT3_spec"
thm MT3.x_def
term MT3.x
(*typedef MT3 = "{(x,y).
  proctype_of x=procedure_type TYPE((bool*unit,string)procedure) \<and>
  proctype_of y=procedure_type TYPE((string*unit,string)procedure) \<and>
  well_typed_proc' (module_type_proc_types TYPE(MT) @ module_type_proc_types TYPE(MT2)) x \<and>
  well_typed_proc' (module_type_proc_types TYPE(MT) @ module_type_proc_types TYPE(MT2)) y}" sorry *)
(*definition "MT3_x (m::MT3) (m1::MT) (m2::MT2) \<equiv>
  case Rep_MT3 m of (x,y) \<Rightarrow> (mk_procedure_typed (subst_proc (module_type_procs m1 @ module_type_procs m2) x) :: (bool*unit,string)procedure)"
definition "MT3_y (m::MT3) (m1::MT) (m2::MT2) \<equiv>
  case Rep_MT3 m of (x,y) \<Rightarrow> (mk_procedure_typed (subst_proc (module_type_procs m1 @ module_type_procs m2) y) :: (string*unit,string)procedure)"*)
(*
instantiation MT3 :: module_type begin
definition "module_type_procs_MT3 (m::MT3) == case Rep_MT3 m of (x,y) \<Rightarrow> [x,y]" 
definition "module_type_proc_names_MT3 (_::MT3 itself) == [[''x''],[''y'']]" 
definition "module_type_proc_types_MT3 (_::MT3 itself) == [procedure_type TYPE((bool*unit,string)procedure), procedure_type TYPE((string*unit,string)procedure)]" 
instance apply intro_classes sorry
end
*)

