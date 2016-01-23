theory Scratch2
imports Main Rewrite
begin

ML "open Rewrite"

lemma 
  fixes x :: nat
  assumes x: "x=2"
  shows "4*4=8"
  apply (rewrite at 4 eq_reflection)
proof -

ML_val {*
  val pat = [At, Term (@{term "4::nat"},[])]
  val res = rewrite_conv @{context} (pat,NONE) @{thms eq_reflection}
            @{cterm "4*4=8"}
*}
  apply (rewrite at x x)
  



ML {*
  val pc0 : Rewrite.patconv = rewrs_pconv NONE @{thms refl}
  val pc : Rewrite.patconv =  pc0 
  (* |> (fn p => Rewrite.match_pconv p (@{term "5::int"},[]))  *)
  |> params_pconv o concl_pconv
  (* |> in_pconv *)
;;
  
  pc
  @{context} (Vartab.empty,[]) @{cterm "x*5=x"}
*}


ML
module_type ('pk) EncScheme =
  keygen :: "(unit,unit) procedure"

module_type 'a XX = f :: "(unit,unit)procedure"

(* declare [[ML_exception_trace]] *)
ML "open Procs_Typed"

local_setup {* fn lthy =>
  let
val spec = {name= @{binding X}, procedures=[], type_params=[]}
val rep_binding = Binding.suffix_name "_rep" (#name spec)
      val tparams = map fst (#type_params spec)
      val proctypes = map snd (#procedures spec)
      val proctypes_tuple = HOLogic.mk_tupleT proctypes

      val lthy_start = lthy

      (* Declaring: type_synonym ('a,'b) ModuleType_rep = "(unit,unit) procedure * (unit,'b) procedure" *)
      val (rep_type_name,lthy) = Typedecl.abbrev (rep_binding,tparams,NoSyn) proctypes_tuple lthy
      val rep_type = Type(rep_type_name, map TFree (#type_params spec))

      (* Declaring: typedef ('a,'b) ModuleType = "UNIV :: ('a::prog_type,'b::prog_type) ModuleType_rep set" *)
      val typedef_repset = HOLogic.mk_UNIV (rep_type)
      val ((abs_type_name,typedef_info),lthy) = 
(* TODO: is overloaded necessary? https://groups.google.com/forum/#!topic/fa.isabelle/Azn3NBvNSgM *)
          Typedef.add_typedef {overloaded=true} (#name spec, #type_params spec, NoSyn)
              typedef_repset NONE (fn ctx => (resolve_tac ctx @{thms UNIV_witness} 1)) lthy
      val abs_type = Type(abs_type_name, map TFree (#type_params spec))
      (* val Rep_MT = Const(#Rep_name (fst typedef_info),abs_type --> rep_type) *)
      val Abs_MT = Const(#Abs_name (fst typedef_info),rep_type --> abs_type)

      fun export thm = thm (* Proof_Context.export lthy lthy_start [thm] |> hd *)

      (* Declaring: instantiation ModuleType = (...)procedure_type begin ... end *)

  in  lthy  end
*}


ML {*
Thm.instantiate' [SOME @{ctyp "'abs::type"}, SOME @{ctyp "'rep::procedure_functor"}] [] @{thm OFCLASS_procedure_functor_class_I}
*}

ML {* *}

instantiation X :: procedure_functor begin

(* definition "procedure_functor_type_X == \<lambda>_::X itself. procedure_functor_type (TYPE(X_rep))" *)
(* term "procedure_functor_type_X" *)
(* thm "procedure_functor_type_X_def" *)

local_setup {* fn lthy => let
      val pftype_bind = @{binding "procedure_functor_type_X"}
val lthy0 = lthy
      val ((a,(b,c)),lthy) = Local_Theory.define
          ((pftype_bind,NoSyn), 
           ((Thm.def_binding pftype_bind,[]),
             @{termx "\<lambda>_::X itself. procedure_functor_type (TYPE(X_rep))"})) lthy
val _ = @{print} a
val _ = @{print} b
val _ = @{print} (Thm.prop_of c)
val glthy = lthy |> Proof_Context.theory_of |> Proof_Context.init_global
val c' = glthy |> (fn ctx => Proof_Context.get_thm ctx "procedure_functor_type_X_def")
val c' = glthy |> (fn ctx => Proof_Context.get_thm ctx "procedure_functor_type_X_def")
val [c'] = Proof_Context.export lthy glthy [c]
val _ = @{print} (Thm.prop_of c')
in lthy end
*}

ML {* Thm.prop_of @{thm  procedure_functor_type_X_def} *}

local_setup {*
fn lthy =>
  let
(*   val bind = @{binding X}
  val rep_type = @{typ X_rep}
  val AbsF = @{term Abs_X} 
  val RepF = @{term Rep_X}
  val Abs_inverse = @{thm Abs_X_inverse}
  val Rep_inverse = @{thm Rep_X_inverse} 
 *)
  (* val abs_type = @{typ X} *)

val export_target = lthy

       (* Declaring: definition "procedure_functor_type_AbsType (x::('a,'b) AbsType itself) == procedure_functor_type (TYPE(RepType))" *)
(*       val pftype_bind = @{binding "procedure_functor_type_X"}
      val ((_,(_,pftype_def)),lthy) = Local_Theory.define
          ((pftype_bind,NoSyn), 
           ((Thm.def_binding pftype_bind,[]),
             @{termx "\<lambda>_::X itself. procedure_functor_type (TYPE(X_rep))"})) lthy
 *) 

 val pftype_def = @{thm procedure_functor_type_X_def} 
val _ = @{print} (Thm.prop_of pftype_def)

(*       (* Declaring: definition "procedure_functor_mk_untyped_AbsType x == procedure_functor_mk_untyped (Rep x)" *)
      val pfmkuntyped_bind = Binding.prefix_name "procedure_functor_mk_untyped_" bind
      val ((_,(_,pfmkuntyped_def)),lthy) = Local_Theory.define
          ((pfmkuntyped_bind,NoSyn), 
           ((Thm.def_binding pfmkuntyped_bind,[]),
             @{termx "\<lambda>x::?'abs_type. procedure_functor_mk_untyped (?RepF x :: ?'rep_type::procedure_functor)"})) lthy

      (* Declaring: definition "procedure_functor_mk_typed'_AbsType p == Abs (procedure_functor_mk_typed' p)" *)
      val pfmktyped_bind = Binding.prefix_name "procedure_functor_mk_typed'_" bind
      val ((_,(_,pfmktyped_def)),lthy) = Local_Theory.define
          ((pfmktyped_bind,NoSyn), 
           ((Thm.def_binding pfmktyped_bind,[]),
             @{termx "\<lambda>p. ?AbsF (procedure_functor_mk_typed' p :: ?'rep_type::procedure_functor) :: 'abs_type"})) lthy *)

val _ = writeln ("pftype_def "^Thm.string_of_thm @{context} pftype_def)

      val OFCLASS_I = Thm.instantiate' [NONE, SOME (Thm.ctyp_of lthy @{typ X_rep})] []
          @{thm OFCLASS_procedure_functor_class_I}



(* val _ = writeln (Thm.string_of_thm @{context} OFCLASS_I) *)

      (* val export_target = Proof_Context.init_global thy *)
val export_target = lthy |> Proof_Context.theory_of |> Proof_Context.init_global
      fun export thm = Variable.export lthy export_target [thm] |> hd

val pftype_def' = pftype_def |> export

val _ = writeln "XXXyyy"
      fun instance_tac ctx = 
        resolve_tac ctx [OFCLASS_I] 1
THEN print_tac ctx "xxx"
            THEN solve_tac ctx [pftype_def'] 1
THEN print_tac ctx "yyy"
 (*            THEN solve_tac ctx [pfmkuntyped_def] 1
            THEN solve_tac ctx [pfmktyped_def] 1
            THEN solve_tac ctx [Abs_inverse] 1
            THEN solve_tac ctx [Rep_inverse] 1 *)

       val lthy = Class.prove_instantiation_instance instance_tac lthy  
in (lthy) end
*}

ML Class.prove_instantiation_instance
ML {* Thm.prop_of @{thm procedure_functor_type_X_def} *}
instance
apply (rule OFCLASS_procedure_functor_class_I)









instantiation X :: procedure_functor begin
local_setup {* fn lthy =>
loc_instantiate_type_copy_procedure_functor  lthy
*}
end

ML {* 
fun instantiate_type_copy_procedure_functor bind abs_type_name tparams rep_type AbsF RepF Abs_inverse Rep_inverse thy =
  let val lthy = Class.instantiation ([@{type_name X}], [], @{sort procedure_functor}) thy
      val (tmp,lthy) = loc_instantiate_type_copy_procedure_functor bind abs_type_name tparams rep_type AbsF RepF Abs_inverse Rep_inverse lthy
      val thy = Local_Theory.exit_global lthy
  in (tmp,thy) end
      val inst_global : theory -> (thm*thm*thm)*theory = instantiate_type_copy_procedure_functor 
          @{binding X} @{type_name X} [] @{typ X_rep}
          @{term Abs_X} @{term Rep_X}
          @{thm Abs_X_inverse} @{thm Rep_X_inverse}
 *}


local_setup {* fn lthy =>                                            
let



      val (_,lthy) = Local_Theory.background_theory_result inst_global lthy
in lthy end
*}



(* local_setup {*
declare_module_type {name= @{binding XX}, procedures=[], type_params=[]}
*}
 *)
(* local_setup {*
declare_module_type_cmd @{binding X} [] [] 
*}

module_type XX = f :: "(unit,unit)procedure"
 *)

end