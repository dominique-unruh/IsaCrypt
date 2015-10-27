structure Procs_Typed = 
struct

(** procedure_info **)

type procedure_info = {
  pattern : cterm,
  args : thm option,
  body : thm option,
  return : thm option,
  body_local_vars : thm option,
  return_vars : thm option
};

fun procedure_info_same_pattern (a,b) = Thm.term_of (#pattern a) aconv Thm.term_of (#pattern b)

structure ProcedureData = Generic_Data
  (type T = procedure_info Net.net
   val empty = Net.empty
   val extend = I
   val merge = Net.merge procedure_info_same_pattern)

fun morphism_procedure_info phi ({args,body,return,body_local_vars,return_vars,pattern} : procedure_info) =
  let val f = Option.map (Morphism.thm phi)
      val f2 = Morphism.cterm phi
  in
  { args=f args, body=f body, body_local_vars=f body_local_vars, return_vars=f return_vars, 
    return=f return, pattern=f2 pattern
  } : procedure_info
  end

fun register_procedure info =
  Local_Theory.declaration {pervasive=true, syntax=false}
  (fn phi => 
    let val info' = morphism_procedure_info phi info
        val pattern = Thm.term_of (#pattern info')
    in ProcedureData.map (Net.insert_term procedure_info_same_pattern (pattern,info')) end);


fun trivial_procedure_info (ctx:Proof.context) (p:term) : procedure_info =
  { pattern = Thm.cterm_of ctx p,
    args=NONE,
    body=NONE,
    body_local_vars=NONE,
    return=NONE,
    return_vars=NONE
  };


(* fun procedure_head_of ctx (Const(@{const_name procfun_apply},_) $ p $ _) = procedure_head_of ctx p
  | procedure_head_of ctx (p $ _) = procedure_head_of ctx p
  | procedure_head_of _ (Const(name,_)) = name
  | procedure_head_of _ (Abs _) = error "procedure_head_of Abs"
  | procedure_head_of _ (Var _) = error "procedure_head_of Var"
  | procedure_head_of _ (Free _) = error "procedure_head_of Free"
  | procedure_head_of _ (Bound _) = error "procedure_head_of Bound" *)

fun assert_procedure_info_complete ctx ({args=_,body=_,body_local_vars, pattern=_, return=_, return_vars} : procedure_info) = 
  let fun is_string_literal n = (HOLogic.dest_string n; true) handle TERM _ => false
      fun is_var (v as (Const(@{const_name mk_variable_untyped},_) $ (Const(@{const_name LVariable},_) $ n))) =
              if is_string_literal n then () else error ("Not a variable: "^Syntax.string_of_term ctx v)
        | is_var (v as (Const(@{const_name mk_variable_untyped},_) $ (Const(@{const_name Variable},_) $ n))) =
              if is_string_literal n then () else error ("Not a variable: "^Syntax.string_of_term ctx v)
        | is_var t = error ("not a var: "^Syntax.string_of_term ctx t)
      fun is_varset (Const(@{const_name insert},_) $ v $ s) = (is_var v; is_varset s)
        | is_varset (Const(@{const_name Orderings.bot_class.bot},_)) = ()
        | is_varset t = error ("not a varset: "^Syntax.string_of_term ctx t)
      fun rhs thm = Thm.prop_of thm |> Logic.dest_equals |> snd
      fun is_varset_thm NONE = ()
        | is_varset_thm (SOME thm) = is_varset (rhs thm)
      val _ = is_varset_thm body_local_vars
      val _ = is_varset_thm return_vars
  in ()
  end

fun get_procedure_info lthy partial proc = 
  let val _ = tracing ("Constructing procedure info for "^Syntax.string_of_term lthy proc)
      (* val name : string = procedure_head_of lthy proc *)
      val cproc = Thm.cterm_of lthy proc
      val infos = Net.match_term (ProcedureData.get (Context.Proof lthy)) proc
                  |> map_filter (fn info => SOME (info,Thm.first_order_match (#pattern info, cproc))
                    handle Pattern.MATCH => NONE)
(*       val info = case info of SOME info => info 
                            | NONE => if partial then trivial_procedure_info lthy proc
                                      else error ("Could not find procedure_info for procedure "^name)
      val matcher = Thm.first_order_match (#pattern info, cproc)
                    handle Pattern.MATCH => error ("get_procedure_info: cannot match "
                      ^Pretty.string_of (Syntax.pretty_term lthy proc)^" with "
                      ^Pretty.string_of (Syntax.pretty_term lthy (Thm.term_of (#pattern info)))) *)
      val _ = if null infos then error ("Could not find procedure_info for procedure pattern "^Syntax.string_of_term lthy proc) else ()
      val (info,matcher) = hd infos
      val _ = if not (null (tl infos)) then warning ("Several matchin procedure infos for "^ 
                                               Syntax.string_of_term lthy proc^
                                               ": "^String.concatWith ", " (map (Syntax.string_of_term lthy o Thm.term_of o #pattern o fst) infos)^
                                               ". Picking first one.")
              else ()
      fun inst thm = Option.map (Thm.instantiate matcher) thm handle Match => error "Match"
      val info : procedure_info = {
        pattern = #pattern info |> Thm.instantiate_cterm matcher,
        args = #args info |> inst, body = #body info |> inst,
        body_local_vars = #body_local_vars info |> inst,
        return_vars = #return_vars info |> inst, return = #return info |> inst }
      val _ = if (Thm.term_of (#pattern info)) aconv proc then () else error "bad instatiation"
      val _ = if not partial then assert_procedure_info_complete lthy info else ()
  in
    info
  end

open Conv

fun register_procedure_thm thm lthy = 
  let val thm' = case Thm.concl_of thm of
                   (Const ("Pure.eq", _) $ _ $ _) => thm
                 | _ => thm RS @{thm eq_reflection}
      fun unfold th = top_sweep_conv (K (rewr_conv th)) lthy (* TODO: should fail if no occurrence *)
      val pattern = thm' |> Thm.concl_of |> Logic.dest_equals |> fst

      val _ = writeln ("Registering procedure "^Syntax.string_of_term lthy pattern)

      val return = @{termx "p_return (?pattern::(?'a::prog_type, ?'b::prog_type) procedure)"
                      where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold thm' then_conv unfold @{thm p_return_simp})

      val body = @{termx "p_body (?pattern::(?'a::prog_type, ?'b::prog_type) procedure)"
                      where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold thm' then_conv unfold @{thm p_body_simp})

      val args = @{termx "p_arg (?pattern::(?'a::prog_type, ?'b::prog_type) procedure)"
                      where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold thm' then_conv unfold @{thm p_arg_simp})

      val return_vars = @{termx "set (e_vars (p_return (?pattern::(?'a::prog_type, ?'b::prog_type) procedure)))"
                          where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold return then_conv Simplifier.rewrite lthy)

(*      val body_vars = @{termx "set (vars (p_body (?pattern::(?'a::procargs, ?'b::prog_type) procedure)))"
                          where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold body then_conv Simplifier.rewrite lthy) *)

      val simpset = lthy addsimps @{thms vars_proc_global_locals}
      val body_local_vars = @{termx "set (local_vars (p_body (?pattern::(?'a::prog_type, ?'b::prog_type) procedure)))"
                          where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold body
                then_conv unfold @{thm local_vars_def[THEN eq_reflection]} 
                then_conv Simplifier.rewrite simpset)
      (* val name = procedure_head_of lthy pattern *)
  in
  register_procedure {
    pattern=Thm.cterm_of lthy pattern,
    body=SOME body, return=SOME return, args=SOME args,
    body_local_vars=SOME body_local_vars, return_vars=SOME return_vars
  } lthy
  end



(** definition of procedures **)

fun match_inst_tac ctx thms i =
  match_tac ctx thms i THEN rtac @{thm refl} i

fun procedure_existence_solve_tac' ctx safe unsafe i =
  ((match_inst_tac ctx safe
    ORELSE' match_inst_tac ctx unsafe) THEN_ALL_NEW procedure_existence_solve_tac' ctx safe unsafe) i

fun procedure_existence_tac' ctx safe unsafe i = 
(* print_tac ctx "procedure_existence_tac:GOAL"  THEN *)
(
  (match_inst_tac ctx safe THEN_ALL_NEW procedure_existence_tac' ctx safe unsafe) i
  ORELSE (match_inst_tac ctx unsafe THEN_ALL_NEW procedure_existence_solve_tac' ctx safe unsafe) i
  ORELSE all_tac
);;

fun procedure_existence_tac ctx = procedure_existence_tac' ctx
  (Named_Theorems.get ctx "Procs_Typed.reduce_procfun.safe") 
  (Named_Theorems.get ctx "Procs_Typed.reduce_procfun.unsafe")

fun split_conjunction_tac i = 
  (rtac @{thm conjunctionI} THEN_ALL_NEW split_conjunction_tac) i
  ORELSE all_tac

fun definition_via_specification_tac tac ctx =
  ALLGOALS split_conjunction_tac
  THEN ALLGOALS (dtac meta_eq_to_obj_eq)
  THEN ALLGOALS (hyp_subst_tac_thin true ctx)
  THEN ALLGOALS (tac ctx)

(* Instantiates all schematic term variables in t with "undefined" *)
fun instantiate_schematics (t$u) = instantiate_schematics t $ instantiate_schematics u
  | instantiate_schematics (Abs(x,T,t)) = Abs(x,T,instantiate_schematics t)
  | instantiate_schematics (t as Free _) = t
  | instantiate_schematics (t as Bound _) = t
  | instantiate_schematics (t as Const _) = t
  | instantiate_schematics (Var(_,T)) = Const(@{const_name undefined},T)

fun definition_via_specification tac (consts:((binding * typ) * mixfix) list) 
  (props: (Attrib.binding * term) list)(lthy:Proof.context) = 
let val schema_eqs = consts |> map (fn ((b,T),_) => 
            Logic.mk_equals (Free(Binding.name_of b,T), Var ((Binding.name_of b,0),T)))
    val const_names = consts |> map (fn ((b,_),_) => Binding.name_of b)
    val bindings = props |> map fst |> map fst
    (* val prop = Logic.mk_conjunction_list (map snd props) *)
    val props = map snd props
    val frees = fold Term.add_frees props [] |> 
      filter (fn(n,_) => not (Variable.is_fixed lthy n)) |>
      filter (fn(n,_) => not (member (op=) const_names n)) |>
      map Free
    val def_thm_props = map (fn prop => Logic.list_implies (schema_eqs, prop)) props
    val def_thm_props = map (fn p => fold Logic.all frees p) def_thm_props
    (*val def_thm_prop = def_thm_prop |> fold Logic.all consts (* ??? keep ? *) *)
    
    fun lhs_to_binding thm =
      let fun l (Const(n,_)) = [Long_Name.base_name n]
            | l (Const(@{const_name procfun_apply},_) $ a $ b) = l a @ l b
            | l (a $ b) = l a @ l b
            | l (Free(n,_)) = [n]
            | l (Var _) = []
            | l (Bound _) = []
            | l (Abs (_,_,t)) = l t
          val lhs = case Thm.prop_of thm of
                      Const(@{const_name Trueprop},_) $ (Const(@{const_name "HOL.eq"},_) $ lhs $ _) => lhs
                    | Const(@{const_name Pure.eq},_) $ lhs $ _ => lhs
                    | _ => raise THM ("Please specify a binding for specifications (can't extract lhs for autogenerated name)",0,[thm])
          val str_list = l lhs @ ["def"]
          val const_bind = consts |> hd |> fst |> fst
          val name = String.concatWith "_" str_list
          val binding = Binding.map_name (K name) const_bind
      in
         binding
      end

    fun get_binding thm binding =
      if Binding.is_empty binding
      then lhs_to_binding thm
      else binding

    fun after_qed thms lthy = 
    let
      val def_thms = thms |> hd
      val rhs = def_thms |> hd |> Thm.legacy_freezeT |> Thm.prop_of |> Logic.strip_assums_hyp |> take (length consts)
                |> map (snd o Logic.dest_equals)
                |> map instantiate_schematics (* Else the definition fails if schematic vars were introduced*)
      val (raw_thms,lthy) = fold2 (fn const => fn rhs => fn (raw_thms,lthy) =>
          let val ((bind,_),syn) = const
              val ((_,(_,thm)),lthy) = Local_Theory.define
                  ((bind,syn), ((Binding.suffix_name "_def_raw" bind,[]),rhs)) lthy
          in (thm::raw_thms,lthy) end) consts rhs ([],lthy)
      val final_thms = map (fold (fn def => fn thm => thm OF [def]) raw_thms) def_thms
      (* val bind_thm = consts |> hd |> fst |> fst |> Thm.def_binding *)
      val final_thms_bindings = map (fn (thm,bind) => (thm,get_binding thm bind)) (ListPair.zip (final_thms,bindings))
      (* Declare the specification terms as lemmas *)
      val lthy = fold (fn (thm,bind) => snd o Local_Theory.note ((bind,[]), [thm])) final_thms_bindings lthy 
      (* Register procedure infos for the generated declarations *)
      val lthy = fold register_procedure_thm final_thms lthy
    in lthy end

    val method : Method.text = tac lthy
                 |> SIMPLE_METHOD |> K |> Method.Basic
    val state = Proof.theorem NONE after_qed [map (fn p => (p,[])) def_thm_props] lthy
    val state = Proof.apply method state |> Seq.hd 
                handle Option => state
in state end

fun definition_via_specification_solve tac consts prop lthy =
  let val state = definition_via_specification tac consts prop lthy
      val lthy = Proof.global_done_proof state
  in lthy end

(* val variables_parser : (binding * string option * mixfix) list parser =
    Scan.optional (Parse.$$$ "(" |--
      Scan.optional (Parse.reserved "globals" |-- Parse.fixes) []
    --| Parse.$$$ ")") [] *)

val procedure_parser =
  Parse.fixes --
  (Parse.$$$ "where" |-- 
    Parse.!!! (Parse.and_list1
      (Parse_Spec.opt_thm_name ":" -- Parse.prop)))

fun procedure_cmd dvs (consts,props) ctx =
  let val ((consts,props),_) = Specification.read_free_spec consts props ctx
  in dvs consts props ctx end;

val _ = Outer_Syntax.local_theory @{command_keyword procedure}
"definition of procedures / modules"
(procedure_parser >>
   procedure_cmd (definition_via_specification_solve 
      (definition_via_specification_tac procedure_existence_tac)))

val _ = Outer_Syntax.local_theory_to_proof @{command_keyword procedure'}
"definition of procedures / modules (with proof obligation)"
(procedure_parser >>
   procedure_cmd (definition_via_specification 
      (definition_via_specification_tac procedure_existence_tac)))

(** Definition of module types **)

fun instantiate_type_copy_procedure_functor bind abs_type_name tparams rep_type AbsF RepF Abs_inverse Rep_inverse thy 
  : (thm*thm*thm) * theory
=
  let (* Declaring: instantiation ModuleType :: (prog_type,prog_type)procedure_functor_type *)
      val lthy = Class.instantiation ([abs_type_name], tparams, @{sort procedure_functor}) thy

      val abs_type = Type(abs_type_name,map TFree tparams)

      (* Declaring: definition "procedure_functor_type_AbsType (x::('a,'b) AbsType itself) == procedure_functor_type (TYPE(RepType))" *)
      val pftype_bind = Binding.prefix_name "procedure_functor_type_" bind
      val ((_,(_,pftype_def)),lthy) = Local_Theory.define
          ((pftype_bind,NoSyn), 
           ((Thm.def_binding pftype_bind,[]),
             @{termx "\<lambda>_::?'abs_type itself. procedure_functor_type (TYPE(?'rep_type::procedure_functor))"})) lthy

      (* Declaring: definition "procedure_functor_mk_untyped_AbsType x == procedure_functor_mk_untyped (Rep x)" *)
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
             @{termx "\<lambda>p. ?AbsF (procedure_functor_mk_typed' p :: ?'rep_type::procedure_functor) :: 'abs_type"})) lthy

      val export_target = Proof_Context.init_global thy
      fun export thm = Proof_Context.export lthy export_target [thm] |> hd

      (* Declaring: instance apply (rule OFCLASS_procedure_functor_class_I)
                             apply (fact procedure_functor_type_AbsType_def)
                             apply (fact procedure_functor_mk_untyped_AbsType_def)
                             apply (fact procedure_functor_mk_typed'_AbsType_def)
                             apply (fact Abs_inverse apply (fact Rep_inverse) *)

      val pftype_def = export pftype_def
      val pfmktyped_def = export pfmktyped_def
      val pfmkuntyped_def = export pfmkuntyped_def

      fun instance_tac ctx = 
        rtac @{thm OFCLASS_procedure_functor_class_I} 1
            THEN solve_tac ctx [pftype_def] 1
            THEN solve_tac ctx [pfmkuntyped_def] 1
            THEN solve_tac ctx [pfmktyped_def] 1
            THEN solve_tac ctx [Abs_inverse] 1
            THEN solve_tac ctx [Rep_inverse] 1
      val thy = Class.prove_instantiation_exit instance_tac lthy
in ((pftype_def,pfmkuntyped_def,pfmktyped_def),thy) end


type module_type_spec = {
  name : binding,
  type_params : (string*sort) list,
  procedures : (binding * typ) list
}


fun nth_of_m_procfun 0 1 f = f
  | nth_of_m_procfun 0 m f =
      if m<=0 then error "nth_of_m_procfun: m\<le>0" 
      else @{termx "procfun_compose <$> fst_procfun <$> (?f::?'f.1)" 
             where "?'f.1\<Rightarrow>?'a::procedure_functor=proc=>(?'b::procedure_functor*?'c::procedure_functor)"}
  | nth_of_m_procfun n m f =
      if n<0 then error "nth_of_m_procfun: n<0"
      else if m<=n then error "nth_of_m_procfun: n\<ge>m"
      else nth_of_m_procfun (n-1) (m-1)
            @{termx "procfun_compose <$> snd_procfun <$> (?f::?'f.1)" 
             where "?'f.1\<Rightarrow>?'a::procedure_functor=proc=>(?'b::procedure_functor*?'c::procedure_functor)"}


(* Example: spec = {name = @{binding ModuleType},
                    type_params = [("'a",@{sort prog_type}), ("'b",@{sort prog_type})],
                    procedures = [(@{binding proc1}, @{typ "(unit,unit) procedure"}),
                                  (@{binding proc2}, @{typ "(unit,'b) procedure"})]} *)

fun declare_module_type (spec:module_type_spec) lthy =
  let val rep_binding = Binding.suffix_name "_rep" (#name spec)
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
          Typedef.add_typedef false (#name spec, #type_params spec, NoSyn)
              typedef_repset NONE (K (rtac @{thm UNIV_witness} 1)) lthy
      val abs_type = Type(abs_type_name, map TFree (#type_params spec))
      (* val Rep_MT = Const(#Rep_name (fst typedef_info),abs_type --> rep_type) *)
      val Abs_MT = Const(#Abs_name (fst typedef_info),rep_type --> abs_type)

      fun export thm = Proof_Context.export lthy lthy_start [thm] |> hd

      (* Declaring: instantiation ModuleType = (...)procedure_type begin ... end *)
      val inst_global : theory -> (thm*thm*thm)*theory = instantiate_type_copy_procedure_functor 
          (#name spec) abs_type_name (#type_params spec) rep_type
          (Const(#Abs_name (fst typedef_info), rep_type --> abs_type))
          (Const(#Rep_name (fst typedef_info), abs_type --> rep_type))
          (#Abs_inverse (snd typedef_info) |> export) (#Rep_inverse (snd typedef_info) |> export)
      val ((pftype_def,pfmkuntyped_def,pfmktyped_def),lthy) = Local_Theory.background_theory_result inst_global lthy

      (* Declaring: definition Abs_ModuleType' :: "('a,'b) ModuleType_rep =proc=> ('a,'b) ModuleType" where
                    "Abs_ModuleType' = Abs_procfun (ProcAbs (ProcRef 0))" *)
      val Abs_MT'_bind = #name spec |> Binding.prefix_name "Abs_" |> Binding.suffix_name "'"
      val ((_,(_,Abs_MT'_def)),lthy) = Local_Theory.define
          ((Abs_MT'_bind,NoSyn), 
           ((Thm.def_binding Abs_MT'_bind,[]),
             @{termx "Abs_procfun (ProcAbs (ProcRef 0)) 
                 :: ?'rep_type::procedure_functor =proc=> ?'abs_type::procedure_functor"})) lthy

      (* Declaring: definition Rep_ModuleType' :: "('a,'b) ModuleType_rep =proc=> ('a,'b) ModuleType" where
                    "Rep_ModuleType' = Rep_procfun (ProcRep (ProcRef 0))" *)
      val Rep_MT'_bind = #name spec |> Binding.prefix_name "Rep_" |> Binding.suffix_name "'"
      val ((Rep_MT'_t,(_,Rep_MT'_def)),lthy) = Local_Theory.define
          ((Rep_MT'_bind,NoSyn), 
           ((Thm.def_binding Rep_MT'_bind,[]),
             @{termx "Abs_procfun (ProcAbs (ProcRef 0)) 
                 :: ?'abs_type::procedure_functor =proc=> ?'rep_type::procedure_functor"})) lthy

      (* Declaring: lemma Rep_ModuleType': "procfun_apply Rep_ModuleType' = Rep_ModuleType" *) 
      val Rep_MT'_thm = @{thm Rep_ModuleType'_template} OF [Rep_MT'_def] OF [pfmkuntyped_def] OF [pftype_def]
      val (_,lthy) = Local_Theory.note ((Rep_MT'_bind,@{attributes [simp]}),[Rep_MT'_thm]) lthy

      (* Declaring: lemma Abs_ModuleType': "procfun_apply Abs_ModuleType' = Abs_ModuleType" *) 
      val Abs_MT'_thm = @{thm Abs_ModuleType'_template} OF [Abs_MT'_def] OF [pfmktyped_def] OF [pftype_def]
      val (_,lthy) = Local_Theory.note ((Abs_MT'_bind,@{attributes [simp]}),[Abs_MT'_thm]) lthy

      val numgetters = length (#procedures spec)
      fun declare_getter (i,proc) lthy : local_theory =
        let val rhs = nth_of_m_procfun i numgetters Rep_MT'_t
            val (bind,_) = proc
            (* Declaring: definition "proc1 == procfun_compose <$> fst_procfun <$> Rep_ModuleType'"
               and similarly for proc2... *)
            val ((getter,(_,getter_def)),lthy) = Local_Theory.define ((bind,NoSyn),((Thm.def_binding bind,[]),rhs)) lthy

            (* Declaring: lemma proc1 [simp]: "proc1 <$> Abs_ModuleType (x,y) = x"
               and similar for proc2... *)
            val proc_vars = #procedures spec |> map (fn(n,T) => (Binding.name_of n,T)) 
                           |> Variable.variant_frees lthy [getter,Abs_MT] |> map Free
            val tuple = HOLogic.mk_tuple proc_vars
            val resultVar = nth proc_vars i
            val prop = @{termx "Trueprop (?getter <$> ((?Abs_MT::_=>?'abs_type::procedure_functor) 
                            (?tuple::?'tuple.1::procedure_functor)) = (?resultVar::?'resultVar.1::procedure_functor))"}
            fun tac {context=ctx,...} = 
              Raw_Simplifier.rewrite_goal_tac ctx 
                [getter_def, @{thm procfun_compose[THEN eq_reflection]}, 
                 Rep_MT'_thm RS @{thm eq_reflection},
                 (#Abs_inverse (snd typedef_info)) OF @{thms UNIV_I} RS @{thm eq_reflection},
                 @{thm fst_procfun[THEN eq_reflection]},
                 @{thm snd_procfun[THEN eq_reflection]},
                 @{thm fst_conv[THEN eq_reflection]},
                 @{thm snd_conv[THEN eq_reflection]}] 1 THEN
              solve_tac ctx @{thms refl} 1
            val thm = Goal.prove lthy (map (fst o Term.dest_Free) proc_vars) [] prop tac
            val (_,lthy) = Local_Theory.note ((bind,@{attributes [simp]}),[thm]) lthy
        in
        lthy
        end

      val lthy = fold_index declare_getter (#procedures spec) lthy


  in  lthy  end


fun declare_module_type_cmd name tparams procedures lthy =
  let val tparams = map (apsnd (Typedecl.read_constraint lthy)) tparams
      (* val lthy = fold (Variable.declare_typ o TFree) tparams lthy *)
      val tparams = map (Proof_Context.check_tfree lthy) tparams
      val procedureTs = Syntax.read_typs lthy (map (fn (_, T, _) => T) procedures)
      val procedureBindings = map (fn (bind,_,_) => bind) procedures
      val procedures = ListPair.zip (procedureBindings, procedureTs)
      val spec = { name = name, type_params = tparams, procedures = procedures }
  in
    declare_module_type spec lthy
  end

val _ = Outer_Syntax.local_theory @{command_keyword module_type} "define a module type"
    (Parse.type_args_constrained -- Parse.binding -- (@{keyword "="} |-- Scan.repeat1 Parse.const_binding)
    >> (fn ((tparams,binding), procedures) => declare_module_type_cmd binding tparams procedures))


end
