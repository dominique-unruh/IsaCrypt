structure Procs_Typed = 
struct


fun procedure_existence_solve_tac ctx i =
  (resolve_tac @{thms reduce_procfun.reduce} THEN_ALL_NEW procedure_existence_solve_tac ctx) i

fun procedure_existence_tac ctx i = 
  (resolve_tac @{thms reduce_procfun.safe} THEN_ALL_NEW procedure_existence_tac ctx) i
  ORELSE (resolve_tac @{thms reduce_procfun.unsafe} THEN_ALL_NEW procedure_existence_solve_tac ctx) i
  ORELSE all_tac;;

fun definition_via_specification_tac tac ctx =
  dtac meta_eq_to_obj_eq 1
  THEN hyp_subst_tac_thin true ctx 1
  THEN tac ctx 1


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
      val rhs = def_thm |> Thm.legacy_freezeT |> prop_of |> Logic.strip_assums_hyp |> take (length consts)
                |> map (snd o Logic.dest_equals)
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

val _ = Outer_Syntax.local_theory @{command_spec "definition_by_specification"}
"definition of simple inductive predicates"
(definition_via_specification_parser >>
   definition_via_specification_cmd (definition_via_specification_solve 
      (definition_via_specification_tac procedure_existence_tac)))

val _ = Outer_Syntax.local_theory_to_proof @{command_spec "definition_by_specification'"}
"definition of simple inductive predicates (with proof obligation)"
(definition_via_specification_parser >>
   definition_via_specification_cmd (definition_via_specification 
      (definition_via_specification_tac procedure_existence_tac)))
end
