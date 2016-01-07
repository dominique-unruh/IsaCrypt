(* -*- mode: sml;-*- *)
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
  mt_make_const: term,
  mt_make_thm: thm,
  mt_constr_const: term,
  mt_constr_def: thm,
  getters: {name: binding, const: term, thm: thm} list,
  MAKE_inverse_lemmas: {name: binding, thm_name: string, thm: thm} list,
  typedef_info: Typedef.info,
  inst_const: term,
  inst_def: thm,
  unmake_const: term,
  unmake_def: thm
};

(* For debugging purposes only! *)
val last_defined_module_type = Unsynchronized.ref (NONE:module_type_info option);

fun mk_nat i = 
  if i=0 then @{term "0::nat"}
  else if i<0 then raise Match
  else @{term "Suc"} $ mk_nat (i-1);;

fun mapi f l =
let fun m _ [] = []
      | m i (a::b) = f i a :: m (i+1) b
in m 0 l end;;

(*fun strip_fun_argsT (Type(@{type_name fun},[_,T])) = strip_fun_argsT T
  | strip_fun_argsT T = T*)

fun Rep (info:Typedef.info) = 
  let val i=fst info in Const(#Rep_name i,#abs_type i --> #rep_type i) end
fun Abs (info:Typedef.info) = 
  let val i=fst info in Const(#Abs_name i,#rep_type i --> #abs_type i) end
fun dest_ModTypeInfo (ModTypeInfo i) = i

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
      val (inst_info:module_type_info option,thy) = 
              if #arguments spec = [] then (NONE,thy)
              else define_module_type {name = Binding.suffix_name "_instantiated" (#name spec),
                                       arguments = [],
                                       procs = #procs spec} thy |> apfst SOME

      (* Contains the procedure / procedure functor types of all functions of the arguments of this module *)
      val env_proc_types = #arguments spec |> map #typ |> map Term.dest_Type |> map fst |>
                           map (fn name => Sign.the_const_type thy (name^".UNMAKE")) |>
                           map Term.dest_funT |> map snd |> map HOLogic.strip_tupleT |> List.concat
      fun env_proc_types_procfunT T = fold_rev (fn a => fn b => Type(@{type_name procfun},[a,b])) env_proc_types T

      (* Perform the equivalent of:
         typedef MT = "module_type_rep_set 
           (module_type_proc_types_open TYPE(arg1) @ ... @ module_type_proc_types_open TYPE(argn))
           [procedure_type TYPE(proctype1), ... , procedure_type TYPE(proctypen)]"
              by (fact module_type_rep_set_inhabited)
      *)
      val env = #arguments spec
                |> map (fn {typ,...} => 
                   @{termx "module_type_proc_types_open TYPE(?'typ::module_type)"})
                |> foldr1 (fn(x,y) => @{termx "?x @ ?y :: procedure_type_open list"})
                   handle List.Empty => @{term "[]::procedure_type_open list"}
      val procTs = #procs spec
                   |> map (fn {typ,...} => @{termx "procedure_type TYPE(?'typ)" where "?'typ\<Rightarrow>(?'a::procargs,?'b::prog_type)procedure"})
                   |> HOLogic.mk_list @{typ "procedure_type"}
      val rep_set = @{term module_type_rep_set} $ env $ procTs
      val ((mt_name,typedef_info),thy) = 
        Typedef.add_typedef_global (#name spec,[],NoSyn) rep_set NONE 
            (rtac @{thm module_type_rep_set_inhabited} 1) thy
      val _ = writeln ("Defined module type "^mt_name)

      val export_target = Proof_Context.init_global thy
      fun export_thm thy thm = case Proof_Context.export thy export_target [thm] of [thm'] => thm' | _ => raise Match
      (* Perform equivalent of:
         instantiation MT :: module_type begin *)
      val thy = Class.instantiation ([mt_name],[],@{sort "module_type"}) thy

      (* definition "module_type_procs_MT == Rep_MT" *)
      val bind = #name spec |> Binding.prefix_name "module_type_procs_"
      val MT = #abs_type (fst typedef_info)
      val Rep_MT = Rep typedef_info
      val ((mt_procs_const,(_,mt_procs_def0)),thy) = Local_Theory.define
          ((bind,NoSyn), ((Thm.def_binding bind,[]), Rep_MT)) thy
      val mt_procs_def = export_thm thy mt_procs_def0

      (* definition "module_type_construct_MT == Abs_MT" *)
      val bind = #name spec |> Binding.prefix_name "module_type_construct_"
      val Abs_MT = Abs typedef_info
      val ((mt_constr_const,(_,mt_constr_def0)),thy) = Local_Theory.define
          ((bind,NoSyn), ((Thm.def_binding bind,[]), Abs_MT)) thy
      val mt_constr_def = export_thm thy mt_constr_def0

      (* definition "module_type_proc_names_MT == %(_::MT itself). [[''b'']]" *)
      val bind = #name spec |> Binding.prefix_name "module_type_proc_names_"
      val rhs = #procs spec |> map (fn p => #name p |> Binding.name_of 
                  |> Long_Name.explode |> map HOLogic.mk_string
                  |> HOLogic.mk_list @{typ id0}) |> HOLogic.mk_list @{typ id}
                  |> Term.absdummy (Term.itselfT MT)
      val ((mt_proc_names_const,(_,mt_proc_names_def0)),thy) = Local_Theory.define
          ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) thy
      val mt_proc_names_def = export_thm thy mt_proc_names_def0

      (* definition "module_type_proc_types_MT == %(_::MT itself). [procedure_type TYPE((...)procedure)]" *)
      val bind = #name spec |> Binding.prefix_name "module_type_proc_types_"
      val rhs = #procs spec |> map #typ |> map (fn typ =>  
                  @{termx "procedure_type TYPE(?'typ)" where "?'typ\<Rightarrow>(?'a::procargs,?'b::prog_type)procedure"})
                  |> HOLogic.mk_list @{typ procedure_type}
                  |> Term.absdummy (Term.itselfT MT)
      val ((mt_proc_types_const,(_,mt_proc_types_def0)),thy) = Local_Theory.define
          ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) thy
      val mt_proc_types_def = export_thm thy mt_proc_types_def0

      (* definition "module_type_environment_MT == %(_::MT itself). module_type_proc_types_open TYPE(MT1) @ ..." *)
      val bind = #name spec |> Binding.prefix_name "module_type_environment_"
      val rhs = env |> Term.absdummy (Term.itselfT MT)
      val ((mt_environment_const,(_,mt_environment_def0)),thy) = Local_Theory.define
          ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) thy
      val mt_environment_def = export_thm thy mt_environment_def0

      (* Perform the rough equivalent of:
         instance apply OFCLASS_module_type[...] by simp_all *)
      local
      val definitional_thms =  
                [mt_procs_def, mt_constr_def, mt_proc_names_def, mt_proc_types_def, mt_environment_def,
                 #Rep (snd typedef_info), #Rep_inverse (snd typedef_info), #Abs_inverse (snd typedef_info) ]
      in
      val OFCLASS_thm = @{thm OFCLASS_module_type} OF definitional_thms
      val thy = Class.prove_instantiation_exit 
            (fn _ => rtac OFCLASS_thm 1 THEN ALLGOALS (simp_tac thy)) thy end

      (* Perform equivalent of:
         instantiation MT :: module_type_closed begin instance ... end
         (if MT is a closed module type)   *)
      val thy = if #arguments spec=[] then
        let val thy = Class.instantiation ([mt_name],[],@{sort "module_type_closed"}) thy
            val definitional_thms = Proof_Context.export thy export_target [mt_environment_def]
            val OFCLASS_closed_thm = @{thm OFCLASS_module_type_closed} OF definitional_thms
            val thy = Class.prove_instantiation_exit (fn _ => 
                rtac OFCLASS_closed_thm 1 THEN
                rtac OFCLASS_thm 1 THEN
                ALLGOALS (simp_tac thy)) thy
        in thy end else thy

      val thy = Named_Target.theory_init thy

      (* For each proci in #procs spec: 
         definition "MT.proci == %(M::MT) (M1::arg1) ... (Mn::argn).
                     (mk_procedure_typed (instantiate_procedure
                         (module_type_procs M1 @ ... @ module_type_procs Mn)
                         ((module_type_procs M)!i)) :: (...)procedure)" 
      *)
      val env_procs = #arguments spec
                |> map (fn {typ,name} => @{termx "module_type_procs::?'typ::module_type\<Rightarrow>_"}
                           $ Free(Binding.name_of name,typ))
                |> foldr1 (fn(x,y) => @{termx "?x @ ?y :: procedure_rep list"})
                   handle List.Empty => @{term "[]::procedure_rep list"}
      val env_proc_vars = #arguments spec
                |> map (fn {typ,name} => (Binding.name_of name,typ))
      val M = Name.variant_list (#arguments spec |> map #name |> map Binding.name_of) [#name spec |> Binding.name_of] |> hd
      val M_Free = Free(M,MT)
      fun define_getter (i,proc as {typ=procT,...}) (getters,thy:local_theory) =
      let val i_nat = mk_nat i
          val rhs = @{termx "mk_procedure_typed (instantiate_procedure ?env_procs 
                               (nth (module_type_procs (?M_Free:: ?'MT::module_type)) ?i_nat)) :: ?'procT" 
                                     where "?'procT\<Rightarrow>(?'a::procargs,?'b::prog_type)procedure"}
          val rhs = rhs |> fold absfree (rev env_proc_vars) |> absfree (M,MT)
          val bind = #name proc |> Binding.qualify true (#name spec |> Binding.name_of)
          val ((getter_const,(_,getter_def)),thy) = Local_Theory.define
              ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) thy
      in ({name= #name proc, const=getter_const, thm=getter_def}::getters,thy) end
      val (getters,thy) = fold_index define_getter (#procs spec) ([],thy)
      val getters = rev getters

      (* definition "MT.MAKE == \<lambda>(proc1::procfun(args,typ1) (proc2::procfun(args,typ2)) ....
            module_type_construct [procedure_functor_mk_untyped proc1, procedure_functor_mk_untyped proc2, ...]" *)
      val proc_vars = #procs spec |> map (fn {name,typ} => (Binding.name_of name,env_proc_types_procfunT typ))
      local
        val rhs = proc_vars |> map Free |> map (fn p => @{termx "procedure_functor_mk_untyped (?p::?'p.1::procedure_functor)"})
              |> HOLogic.mk_list @{typ procedure_rep}
              |> (fn l => @{termx "module_type_construct ?l :: ?'MT::module_type"})
        val rhs = rhs |> fold absfree (rev proc_vars)
        val bind = #name spec |> Binding.qualified true "MAKE" 
      in
      val ((make_const,(_,make_thm)),thy) = Local_Theory.define
              ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) thy end

      (* lemma MT.MAKE.proci: "MT.proci (MT.MAKE proc1 proc2 ...) = proci"
         for each proci *)
      (* TODO: also when not closed \<rightarrow> In this case, the lhs gets module-args, and the rhs gets corresponding proc-fun args *)
      val proc_vars_schematic = map (fn (v,T) => (Var((v,0),T))) proc_vars
      fun MAKE_inverse ({name,const,...},pvar) (lemmas,thy) =
        let val MAKE = fold (fn x => fn f => f$x) proc_vars_schematic make_const
            val prop = Logic.mk_equals (const $ MAKE, pvar)
            val thm = Goal.prove thy [] [] prop (fn _ => Skip_Proof.cheat_tac 1)
                    (* TODO: prove this *)
            val thm_bind = #name spec |> Binding.qualified true "MAKE"
                    |> Binding.qualified true (Binding.name_of name)
            val ((thm_name,thms),thy) = Local_Theory.note ((thm_bind,@{attributes [simp]}),[thm]) thy
        in ({name=name, thm_name=thm_name, thm=hd thms}::lemmas,thy) end
      val (MAKE_inverse_lemmas,thy) = if #arguments spec = []
                then fold MAKE_inverse (ListPair.zip (getters, proc_vars_schematic)) ([],thy)
                else ([],thy)

      (* definition "MT.UNMAKE == \<lambda>M. (module_type_procs m!0, module_type_procs m!1, ...) :: MT \<Rightarrow> procfun(arg,typ1) \<times> ... \<times> procfun(arg,typn)" *)
      local val rhs = #procs spec |> map #typ |> mapi (fn i => fn procT => 
                     let val M=Bound 0 val i' = mk_nat i val procT' = env_proc_types_procfunT procT in
                     @{termx "procedure_functor_mk_typed (module_type_procs (?M::?'MT::module_type) ! ?i') 
                             :: ?'procT'::procedure_functor"} end) 
               |> HOLogic.mk_tuple |> (fn x => Term.Abs("M",MT,x))
            val bind = #name spec |> Binding.qualified true "UNMAKE" 
      in 
      val ((unmake_const,(_,unmake_def)),thy) = Local_Theory.define
              ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) thy
      end
      
      (* definition "MT.inst :: ... \<Rightarrow> MT_instantiated == \<lambda>(M::MT) (M1::arg1) ... (Mn::argn). Abs_MT_instantiated
          (map (instantiate_procedure (module_type_procs M1 @ ... @ module_type_procs Mn))
                (module_type_procs M))"

         (if args=[], it becomes "MT.inst :: MT\<Rightarrow>MT == (\<lambda>x. x))
      *)
      local
          val MT_inst = if #arguments spec = [] then MT
                        else the inst_info |> dest_ModTypeInfo |> #typedef_info |> fst |> #abs_type
          val rhs = if #arguments spec = [] then @{termx "\<lambda>x::?'MT. x"}
              else @{termx "(module_type_construct::_\<Rightarrow>?'MT_inst::module_type) (map (instantiate_procedure ?env_procs)
                      (module_type_procs (?M_Free::?'MT::module_type)))"} |> fold absfree (rev env_proc_vars) |> absfree (M,MT)
          val bind = #name spec |> Binding.qualified true "INST"
      in
      val ((INST_const,(_,INST_def)),thy) = Local_Theory.define
          ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) thy
      end

      val thy = Named_Target.exit thy

      val info = ModTypeInfo {spec=spec, instantiated=inst_info,
          mt_environment_const=mt_environment_const, mt_environment_thm=mt_environment_def,
          mt_proc_types_const=mt_proc_types_const, mt_proc_types_thm=mt_proc_types_def,
          mt_proc_names_const=mt_proc_names_const, mt_proc_names_thm=mt_proc_names_def,
          mt_procs_const=mt_procs_const, mt_procs_thm=mt_procs_def,
          getters=getters, mt_make_const=make_const, mt_make_thm=make_thm,
          MAKE_inverse_lemmas=MAKE_inverse_lemmas, typedef_info=typedef_info,
          inst_const=INST_const, inst_def=INST_def, mt_constr_const=mt_constr_const,
          mt_constr_def=mt_constr_def, unmake_const=unmake_const, unmake_def=unmake_def
          }
      val _ = last_defined_module_type := SOME info
  in
  (info,thy)
  end;


end
