structure Modules =
struct

type module_type_spec = {
  name: binding,
  arguments: {name:binding, typ:typ} list,
  procs: {name:binding, typ:typ} list
};

datatype module_type_info = ModTypeInfo of {
  spec: module_type_spec,
  instantiated: module_type_info option,
  mt_procs_const: term,
  mt_procs_thm: thm,
  mt_environment_const: term,
  mt_environment_thm: thm,
  mt_proc_names_const: term,
  mt_proc_names_thm: thm,
  mt_proc_types_const: term,
  mt_proc_types_thm: thm,
  getters: {const: term, thm: thm} list
};

(* For debugging purposes only! *)
val last_defined_module_type = Unsynchronized.ref (NONE:module_type_info option);

fun mk_nat i = 
  if i=0 then @{term "0::nat"}
  else if i<0 then raise Match
  else @{term "Suc"} $ mk_nat (i-1);;

fun define_module_type (spec:module_type_spec) (thy:theory) : module_type_info*theory =
  let 
      (* Sanity checks on spec *)
      val _ = if has_duplicates (op=) (#arguments spec |> map #name |> map Binding.name_of)
              then raise (ERROR "Two module arguments with the same name")
              else ()
      val _ = if has_duplicates (op=) (#procs spec |> map #name |> map Binding.name_of)
              then raise (ERROR "Two procedures with the same name")
              else ()

      (* Create the module type MT.instantiated (if MT is not closed) *)
      val (inst_info,thy) = 
              if #arguments spec = [] then (NONE,thy)
              else define_module_type {name = Binding.suffix_name "_instantiated" (#name spec),
                                       arguments = [],
                                       procs = #procs spec} thy |> apfst SOME

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
      in ({const=getter_const, thm=getter_def}::getters,thy) end
      val thy = Named_Target.theory_init thy
      val (getters,thy) = fold_index define_getter (#procs spec) ([],thy)
      val thy = Named_Target.exit thy

      val info = ModTypeInfo {spec=spec, instantiated=inst_info,
          mt_environment_const=mt_environment_const, mt_environment_thm=mt_environment_def,
          mt_proc_types_const=mt_proc_types_const, mt_proc_types_thm=mt_proc_types_def,
          mt_proc_names_const=mt_proc_names_const, mt_proc_names_thm=mt_proc_names_def,
          mt_procs_const=mt_procs_const, mt_procs_thm=mt_procs_def,
          getters=getters
          }
      val _ = last_defined_module_type := SOME info
  in
  (info,thy)
  end;


end
