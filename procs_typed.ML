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

structure ProcedureData = Generic_Data
  (type T = procedure_info Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true));

fun morphism_procedure_info phi ({args,body,return,body_local_vars,return_vars,pattern} : procedure_info) =
  let val f = Option.map (Morphism.thm phi)
      val f2 = Morphism.cterm phi
  in
  { args=f args, body=f body, body_local_vars=f body_local_vars, return_vars=f return_vars, 
    return=f return, pattern=f2 pattern
  } : procedure_info
  end

fun register_procedure name info =
  Local_Theory.declaration {pervasive=true, syntax=false}
  (fn phi => ProcedureData.map (Symtab.update (name,morphism_procedure_info phi info)));


fun trivial_procedure_info (ctx:Proof.context) (p:term) : procedure_info =
  { pattern = Thm.cterm_of ctx p,
    args=NONE,
    body=NONE,
    body_local_vars=NONE,
    return=NONE,
    return_vars=NONE
  };


fun procedure_head_of (Const(@{const_name procfun_apply},_) $ p $ _) = procedure_head_of p
  | procedure_head_of (p $ _) = procedure_head_of p
  | procedure_head_of (Const(name,_)) = name
  | procedure_head_of (Abs _) = error "procedure_head_of Abs"
  | procedure_head_of (Var _) = error "procedure_head_of Var"
  | procedure_head_of (Free _) = error "procedure_head_of Free"
  | procedure_head_of (Bound _) = error "procedure_head_of Bound"


fun get_procedure_info lthy partial proc = 
  let val name = procedure_head_of proc
      val cproc = Thm.cterm_of lthy proc
      val info = Symtab.lookup (ProcedureData.get (Context.Proof lthy)) name
      val info = case info of SOME info => info 
                            | NONE => if partial then trivial_procedure_info lthy proc
                                      else error ("Could not find procedure_info for procedure "^name)
      val matcher = Thm.first_order_match (#pattern info, cproc)
                    handle Pattern.MATCH => error ("get_procedure_info: cannot match "
                      ^Pretty.string_of (Syntax.pretty_term lthy proc)^" with "
                      ^Pretty.string_of (Syntax.pretty_term lthy (Thm.term_of (#pattern info))))
      fun inst thm = Option.map (Thm.instantiate matcher) thm handle Match => error "Match"
      val info : procedure_info = {
        pattern = #pattern info |> Thm.instantiate_cterm matcher,
        args = #args info |> inst, body = #body info |> inst,
        body_local_vars = #body_local_vars info |> inst,
        return_vars = #return_vars info |> inst, return = #return info |> inst }
      val _ = if (Thm.term_of (#pattern info)) aconv proc then () else error "bad instatiation"
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

      val return = @{termx "p_return (?pattern::(?'a::procargs, ?'b::prog_type) procedure)"
                      where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold thm' then_conv unfold @{thm p_return_simp})

      val body = @{termx "p_body (?pattern::(?'a::procargs, ?'b::prog_type) procedure)"
                      where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold thm' then_conv unfold @{thm p_body_simp})

      val args = @{termx "p_args (?pattern::(?'a::procargs, ?'b::prog_type) procedure)"
                      where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold thm' then_conv unfold @{thm p_args_simp})

      val return_vars = @{termx "set (e_vars (p_return (?pattern::(?'a::procargs, ?'b::prog_type) procedure)))"
                          where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold return then_conv Simplifier.rewrite lthy)

(*      val body_vars = @{termx "set (vars (p_body (?pattern::(?'a::procargs, ?'b::prog_type) procedure)))"
                          where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold body then_conv Simplifier.rewrite lthy) *)

      val simpset = lthy addsimps @{thms vars_proc_global_locals}
      val body_local_vars = @{termx "set (local_vars (p_body (?pattern::(?'a::procargs, ?'b::prog_type) procedure)))"
                          where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold body
                then_conv unfold @{thm local_vars_def[THEN eq_reflection]} 
                then_conv Simplifier.rewrite simpset)
      val name = procedure_head_of pattern
  in
  register_procedure name {
    pattern=Thm.cterm_of lthy pattern,
    body=SOME body, return=SOME return, args=SOME args,
    body_local_vars=SOME body_local_vars, return_vars=SOME return_vars
  } lthy
  end



(** definition of procedures **)


fun procedure_existence_solve_tac ctx i =
  (resolve_tac ctx @{thms reduce_procfun.reduce} THEN_ALL_NEW procedure_existence_solve_tac ctx) i

fun procedure_existence_tac ctx i = 
print_tac ctx "GOAL"  THEN
(
  (resolve_tac ctx @{thms reduce_procfun.safe} THEN_ALL_NEW procedure_existence_tac ctx) i
  ORELSE (resolve_tac ctx @{thms reduce_procfun.unsafe} THEN_ALL_NEW procedure_existence_solve_tac ctx) i
  ORELSE all_tac
);;

fun definition_via_specification_tac tac ctx =
  dtac meta_eq_to_obj_eq 1
  THEN hyp_subst_tac_thin true ctx 1
  THEN tac ctx 1

(* Instantiates all schematic term variables in t with "undefined" *)
fun instantiate_schematics (t$u) = instantiate_schematics t $ instantiate_schematics u
  | instantiate_schematics (Abs(x,T,t)) = Abs(x,T,instantiate_schematics t)
  | instantiate_schematics (t as Free _) = t
  | instantiate_schematics (t as Bound _) = t
  | instantiate_schematics (t as Const _) = t
  | instantiate_schematics (Var(_,T)) = Const(@{const_name undefined},T)

(*
(* Instantiate all schematic type variables in t. 
   Leaves term unmodified if it cannot find all sort witnesses *)
fun instantiate_schematicsT thy t =
  let val _ = @{print} t
      val tvars = Term.add_tvars t []
      val names = map fst tvars |> @{print}
      val sorts = map snd tvars
      val witn = Sign.witness_sorts thy [] sorts |> map fst
      val t' = subst_TVars (ListPair.zip (names,witn)) t |> Sign.cert_term thy (* TODO: catch errors because of missing witnesses *)
              (* cert_term should never fail. Else: add suitable error checks above *)
  in t' end
*)

fun definition_via_specification tac (consts:((binding * typ) * mixfix) list) 
  (props: (Attrib.binding * term) list)(lthy:Proof.context) = 
let val schema_eqs = consts |> map (fn ((b,T),_) => 
            Logic.mk_equals (Free(Binding.name_of b,T), Var ((Binding.name_of b,0),T)))
    val const_names = consts |> map (fn ((b,_),_) => Binding.name_of b)
    val prop = Logic.mk_conjunction_list (map snd props)
    val frees = Term.add_frees prop [] |> 
      filter (fn(n,_) => not (Variable.is_fixed lthy n)) |>
      filter (fn(n,_) => not (member (op=) const_names n)) |>
      map Free
    val def_thm_prop = Logic.list_implies (schema_eqs, prop)
    val def_thm_prop = def_thm_prop |> fold Logic.all frees
    (*val def_thm_prop = def_thm_prop |> fold Logic.all consts (* ??? keep ? *) *)
    
    fun after_qed thms lthy = 
    let val def_thm = thms |> hd |> hd
      val rhs = def_thm |> Thm.legacy_freezeT |> Thm.prop_of |> Logic.strip_assums_hyp |> take (length consts)
                |> map (snd o Logic.dest_equals)
                |> map instantiate_schematics (* Else the definition fails if schematic vars were introduced*)
      val (raw_thms,lthy) = fold2 (fn const => fn rhs => fn (raw_thms,lthy) =>
          let val ((bind,_),syn) = const
              val ((_,(_,thm)),lthy) = Local_Theory.define
                  ((bind,syn), ((Binding.suffix_name "_def_raw" bind,[]),rhs)) lthy
          in (thm::raw_thms,lthy) end) consts rhs ([],lthy)
      val def_thm_extern = def_thm (* |> singleton (Proof_Context.export ctx lthy) *)
            (* TODO: deal with multi-props \<up>*)
      val final_thm = fold (fn def => fn thm => thm OF [def]) raw_thms def_thm_extern
      val bind_thm = consts |> hd |> fst |> fst |> Thm.def_binding
            (* TODO: use binding given in spec if provided \<up> *)
      val (_,lthy) = Local_Theory.note ((bind_thm,[]), [final_thm]) lthy
    in lthy end

    val method : Method.text = tac lthy
                 |> SIMPLE_METHOD |> K |> Method.Basic
    val state = Proof.theorem NONE after_qed [[(def_thm_prop,[])]] lthy
    val state = Proof.apply method state |> Seq.hd 
                handle Option => state
in state end

fun definition_via_specification_solve tac consts prop lthy =
  let val state = definition_via_specification tac consts prop lthy
      val lthy = Proof.global_done_proof state
  in lthy end

val definition_via_specification_parser =
  Parse.fixes -- (Parse.$$$ "where" |-- Parse.!!! (Parse.enum1 "|"
      (Parse_Spec.opt_thm_name ":" -- Parse.prop)))

fun definition_via_specification_cmd dvs (consts,props) ctx =
  let val ((consts,props),_) = Specification.read_free_spec consts props ctx
  in dvs consts props ctx end;

val _ = Outer_Syntax.local_theory @{command_keyword procedure}
"definition of simple inductive predicates"
(definition_via_specification_parser >>
   definition_via_specification_cmd (definition_via_specification_solve 
      (definition_via_specification_tac procedure_existence_tac)))

val _ = Outer_Syntax.local_theory_to_proof @{command_keyword procedure'}
"definition of simple inductive predicates (with proof obligation)"
(definition_via_specification_parser >>
   definition_via_specification_cmd (definition_via_specification 
      (definition_via_specification_tac procedure_existence_tac)))

end
