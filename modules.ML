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
  mt_make_const: term option,
  mt_make_thm: thm option,
  getters: {name: binding, const: term, thm: thm} list,
  MAKE_inverse_lemmas: {name: binding, thm_name: string, thm: thm} list
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
                   @{termx "module_type_proc_types_open TYPE(?'typ::module_type)"})
                |> foldr1 (fn(x,y) => @{termx "?x @ ?y :: procedure_type_open list"})
                   handle List.Empty => @{term "[]::procedure_type_open list"}
      val procTs = #procs spec
                   |> map (fn {typ,...} => @{termx "procedure_type TYPE(?'typ)" where "?'typ\<Rightarrow>(?'a::procargs,?'b::prog_type)procedure"})
(*Const(@{const_name procedure_type},Term.itselfT typ--> @{typ procedure_type}) $
                                           Logic.mk_type typ) *)
                   |> HOLogic.mk_list @{typ "procedure_type"}
      val rep_set = @{term module_type_rep_set} $ env $ procTs
      val ((mt_name,typdef_info),thy) = 
        Typedef.add_typedef_global (#name spec,[],NoSyn) rep_set NONE 
            (rtac @{thm module_type_rep_set_inhabited} 1) thy
      val _ = writeln ("Defined module type "^mt_name)

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
      val rhs = #procs spec |> map #typ |> map (fn typ =>  
                  @{termx "procedure_type TYPE(?'typ)" where "?'typ\<Rightarrow>(?'a::procargs,?'b::prog_type)procedure"})
(*                  Const(@{const_name procedure_type},Term.itselfT t--> @{typ procedure_type}) $
                      Logic.mk_type t) *)
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

      val thy = Named_Target.theory_init thy

      (* For each proci in #procs spec: 
         definition "MT.proci == %(M::MT) (M1::arg1) ... (Mn::argn).
                     (mk_procedure_typed (subst_proc
                         (module_type_procs M1 @ ... @ module_type_procs Mn)
                         ((module_type_procs M)!i)) :: (...)procedure)" 
      *)
      val env_procs = #arguments spec
                |> map (fn {typ,name} => @{termx "module_type_procs::?'typ::module_type\<Rightarrow>_"}
                   (*Const(@{const_name module_type_procs},typ--> @{typ "procedure_rep list"})*)
                           $ Free(Binding.name_of name,typ))
                |> foldr1 (fn(x,y) => @{termx "?x @ ?y :: procedure_rep list"})
                   handle List.Empty => @{term "[]::procedure_rep list"}
      val env_proc_vars = #arguments spec
                |> map (fn {typ,name} => (Binding.name_of name,typ))
      val M = Name.variant_list (#arguments spec |> map #name |> map Binding.name_of) [#name spec |> Binding.name_of] |> hd
      fun define_getter (i,proc as {typ=procT,...}) (getters,thy:local_theory) =
      let val M_Free = Free(M,MT)
          val i_nat = mk_nat i
          val rhs = @{termx "mk_procedure_typed (subst_proc ?env_procs 
                               (nth (module_type_procs (?M_Free:: ?'MT::module_type)) ?i_nat)) :: ?'procT" 
                                     where "?'procT\<Rightarrow>(?'a::procargs,?'b::prog_type)procedure"}
          val rhs = rhs |> fold absfree (rev env_proc_vars) |> absfree (M,MT)
          val bind = #name proc |> Binding.qualify true (#name spec |> Binding.name_of)
          val ((getter_const,(_,getter_def)),thy) = Local_Theory.define
              ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) thy
      in ({name= #name proc, const=getter_const, thm=getter_def}::getters,thy) end
      val (getters,thy) = fold_index define_getter (#procs spec) ([],thy)
      val getters = rev getters

      (* definition "MT_make == \<lambda>(proc1::typ1) (proc2::typ2) ....
            Abs_MT [mk_procedure_untyped proc1, mk_procedure_untyped proc2, ...]"
         (only if MT is closed) *)
      val proc_vars = #procs spec
              |> map (fn {name,typ} => (Binding.name_of name,typ))
      val rhs = proc_vars |> map (fn p => Const(@{const_name mk_procedure_untyped},snd p--> @{typ procedure_rep})$Free p)
            |> HOLogic.mk_list @{typ procedure_rep}
            |> (fn l => Const(#Abs_name(fst typdef_info),#rep_type(fst typdef_info) --> MT) $ l)
      val rhs = rhs |> fold absfree (rev proc_vars)
      val bind = #name spec |> Binding.qualified true "MAKE" 
      val (make_const,make_thm,thy) =
        if #arguments spec = []
        then let val ((make_const,(_,make_thm)),thy) = Local_Theory.define
              ((bind,NoSyn), ((Thm.def_binding bind,[]), rhs)) thy
             in (SOME make_const, SOME make_thm, thy) end
        else (NONE,NONE,thy)

      (* lemma "MT.proci (MT.MAKE proc1 proc2 ...) = proci"
         for each proci
         (only if MT is closed) *)
      (*val proc_vars_fresh = fold (fn (v,T) => fn (vs,ctx) => 
                                  Name.variant v ctx |> apfst (fn v=>(v,T)::vs))
                            (rev proc_vars) ([],thy)
      val _ = @{print} proc_vars_fresh*)
      val proc_vars_schematic = map (fn (v,T) => (Var((v,0),T))) proc_vars
      fun MAKE_inverse ({name,const,...},pvar) (lemmas,thy) =
        let val MAKE = fold (fn x => fn f => f$x) proc_vars_schematic (the make_const)
            val prop = Logic.mk_equals (const $ MAKE, pvar)
(*            val thm = cterm_of (Proof_Context.theory_of thy) prop |> Goal.init
                    |> Skip_Proof.cheat_tac 1 (* TODO: prove this *)
                    |> Seq.hd |> Goal.finish thy |> Goal.norm_result thy *)
            val thm = Goal.prove thy [] [] prop (fn _ => Skip_Proof.cheat_tac 1)
                    (* TODO: prove this *)
(* apply (unfold MT.a_def MT.MAKE_def module_type_procs_MT_def)
  apply (subst Abs_MT_inverse)
  apply (simp add: subst_proc_empty module_type_rep_set_def)
  apply (simp add: subst_proc_empty) *)
            val thm_bind = #name spec |> Binding.qualified true "MAKE"
                    |> Binding.qualified true (Binding.name_of name)
            val ((thm_name,thms),thy) = Local_Theory.note ((thm_bind,@{attributes [simp]}),[thm]) thy
        in ({name=name, thm_name=thm_name, thm=hd thms}::lemmas,thy) end
      val (MAKE_inverse_lemmas,thy) = if #arguments spec = []
                then fold MAKE_inverse (ListPair.zip (getters, proc_vars_schematic)) ([],thy)
                else ([],thy)

      val thy = Named_Target.exit thy

      val info = ModTypeInfo {spec=spec, instantiated=inst_info,
          mt_environment_const=mt_environment_const, mt_environment_thm=mt_environment_def,
          mt_proc_types_const=mt_proc_types_const, mt_proc_types_thm=mt_proc_types_def,
          mt_proc_names_const=mt_proc_names_const, mt_proc_names_thm=mt_proc_names_def,
          mt_procs_const=mt_procs_const, mt_procs_thm=mt_procs_def,
          getters=getters, mt_make_const=make_const, mt_make_thm=make_thm,
          MAKE_inverse_lemmas=MAKE_inverse_lemmas
          }
      val _ = last_defined_module_type := SOME info
  in
  (info,thy)
  end;


end
