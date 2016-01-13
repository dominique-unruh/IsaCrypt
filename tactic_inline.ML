structure Tactic_Inline =
struct

open Tools

fun has_Bound i t =
  let fun h (Bound i) j = i=j
        | h (Free _) _ = false
        | h (Var _) _ = false
        | h (a$b) i = h a i orelse h b i
        | h (Abs(_,_,t)) i = h t (i+1)
        | h (Const _) _ = false
  in h t i end

fun dest_funCT ct = 
  let val t = Thm.typ_of ct
      val _ = case t of Type("fun",_) => () | _ => raise TYPE("dest_funcT",[t],[])
  in case Thm.dest_ctyp ct of [dom,rng] => (dom,rng) | _ => raise TYPE("dest_funcT",[t],[]) end

val range_funCT = snd o dest_funCT

fun DETERM' tac i = DETERM (tac i)

fun assertion_footprint_tac ctx = SUBGOAL (fn (goal,i) =>
  ((* @{print} (Thm.cterm_of ctx goal); *)
  case goal of
    Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint},_) $ X $ (Abs(v,T,t))) => 
      if not (has_Bound 0 t) then solve_tac ctx @{thms assertion_footprint_const} i
      else (case t of
             Const(@{const_name memory_lookup},_) $ Bound 0 $ _ => resolve_tac ctx @{thms assertion_footprint_lookup} i
           | t1 $ t2 => 
                let val ct1 = Abs(v,T,t1) |> Thm.cterm_of ctx
                    val ct2 = Abs(v,T,t2) |> Thm.cterm_of ctx
                    val ctX = X |> Thm.cterm_of ctx
                    val (a,b) = Thm.ctyp_of_cterm ct1 |> range_funCT |> dest_funCT
                in
                  (resolve_tac ctx [Thm.instantiate' [SOME a, SOME b] [SOME ctX,SOME ct1,SOME ct2]
                    @{thm assertion_footprint_app}] THEN_ALL_NEW assertion_footprint_tac ctx) i
                end
           | _ => raise (TERM( "nyi",[t])))
    | Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint_left},_) $ X $ (Abs(v1,T1,Abs(v2,T2,t)))) => 
      if not (has_Bound 1 t) then ASSERT_SUCCESS' (solve_tac ctx @{thms assertion_footprint_left_const})
                                  (fn t => TERM ("solve_tac assertion_footprint_left_const failed",[t])) i
      else (case t of
             Const(@{const_name memory_lookup},_) $ Bound 1 $ _ => resolve_tac ctx @{thms assertion_footprint_left_lookup} i
           | t1 $ t2 => 
                let val ct1 = Abs(v1,T1,Abs(v2,T2,t1)) |> Thm.cterm_of ctx
                    val ct2 = Abs(v1,T1,Abs(v2,T2,t2)) |> Thm.cterm_of ctx
                    val ctX = X |> Thm.cterm_of ctx
                    val (a,b) = Thm.ctyp_of_cterm ct1 |> range_funCT |> range_funCT |> dest_funCT
                    val rule = Thm.instantiate' [SOME a, SOME b] [SOME ctX,SOME ct1,SOME ct2] @{thm assertion_footprint_left_app}
                in
                  (ASSERT_SUCCESS' (resolve_tac ctx [rule]) (fn t => TERM ("resolve_tac ctx assertion_footprint_left_app failed",[t]))
                   THEN_ALL_NEW assertion_footprint_tac ctx) i
                end
           | _ => raise (TERM( "nyi",[t])))
    | Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint_right},_) $ X $ (Abs(v1,T1,Abs(v2,T2,t)))) => 
      if not (has_Bound 0 t) then ASSERT_SUCCESS' (solve_tac ctx @{thms assertion_footprint_right_const})
                                  (fn t => TERM ("solve_tac assertion_footprint_right_const failed",[t])) i
      else (case t of
             Const(@{const_name memory_lookup},_) $ Bound 0 $ _ => resolve_tac ctx @{thms assertion_footprint_right_lookup} i
           | t1 $ t2 => 
                let val ct1 = Abs(v1,T1,Abs(v2,T2,t1)) |> Thm.cterm_of ctx
                    val ct2 = Abs(v1,T1,Abs(v2,T2,t2)) |> Thm.cterm_of ctx
                    val ctX = X |> Thm.cterm_of ctx
                    val (a,b) = Thm.ctyp_of_cterm ct1 |> range_funCT |> range_funCT |> dest_funCT
                    val rule = Thm.instantiate' [SOME a, SOME b] [SOME ctX,SOME ct1,SOME ct2] @{thm assertion_footprint_right_app}
                in
                  (ASSERT_SUCCESS' (resolve_tac ctx [rule]) (fn t => TERM ("resolve_tac ctx assertion_footprint_right_app failed",[t]))
                   THEN_ALL_NEW assertion_footprint_tac ctx) i
                end
           | _ => raise (TERM( "nyi",[t])))
  | Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint},_) $ _ $ _) => raise (TERM ("handle this case!", [goal]))
  | Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint_left},_) $ _ $ _) => raise (TERM ("handle this case!", [goal]))
  | Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint_right},_) $ _ $ _) => raise (TERM ("handle this case!", [goal]))
  | _ => raise (TERM ("assertion_footprint_tac: expecting a subgoal of the form 'assertion_footprint/assertion_footprint_left/assertion_footprint_right ...'", [goal]))))


(* fun assertion_footprint_tac ctx = 
  let fun app (const,lookup0,lookup1,appl) X (Abs(v,T,t)) i = 
      (if not (has_Bound0 t) then solve_tac ctx [const] i
      else (case t of
             Const(@{const_name memory_lookup},_) $ Bound 0 $ _ => resolve_tac ctx lookup0 i
           | t1 $ t2 => 
                let val ct1 = Abs(v,T,t1) |> Thm.cterm_of ctx
                    val ct2 = Abs(v,T,t2) |> Thm.cterm_of ctx
                    val ctX = X |> Thm.cterm_of ctx
                    val cts = Thm.ctyp_of_cterm ct1 |> Thm.dest_ctyp |> (fn x => nth x 1) |> Thm.dest_ctyp
                in
                  (resolve_tac ctx (Drule.instantiate' [SOME (hd cts), SOME (hd (tl cts))] [SOME ctX,SOME ct1,SOME ct2]
                    appl) THEN_ALL_NEW assertion_footprint_tac ctx) i
                end
           | _ => raise (TERM( "nyi",[t]))))
        | app _ _ _ _ = raise Match (* Cannot happen *)
      val rules = (@{thm assertion_footprint_const},@{thm assertion_footprint_lookup},@{thm refl} (* not used *),@{thm assertion_footprint_app})
      val rules_left = (@{thm assertion_footprint_left_const},@{thm assertion_footprint_left_lookup'},@{thm assertion_footprint_left_lookup},@{thm assertion_footprint_left_app})
  in 
    SUBGOAL (fn (goal,i) =>
      case goal of
        Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint},_) $ X $ (abs as Abs _)) => app rules X abs i
      | Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint_left},_) $ X $ (abs as Abs _)) => app rules_left X abs i
      (* | Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint_right},_) $ X $ (abs as Abs _)) => app rules_right X abs i *)
      | Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint},_) $ _ $ _) => raise (TERM ("handle this case!", [goal]))
      | Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint_left},_) $ _ $ _) => raise (TERM ("handle this case!", [goal]))
      | Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint_right},_) $ _ $ _) => raise (TERM ("handle this case!", [goal]))
      | _ => raise (TERM ("assertion_footprint_tac: expecting a subgoal of the form 'assertion_footprint/assertion_footprint_left/assertion_footprint_right ...'", [goal])))
  end
 *)

fun string_of_varlist ctx vs =
  (String.concatWith "\n" 
  (map (fn t => case t of _$v => Syntax.string_of_term ctx t ^ " (" ^ Syntax.string_of_typ ctx (fastype_of v) ^ ")"
                        | _ => Syntax.string_of_term ctx t)  vs))


(* "NGOALS i n tac" applies tac to goals i+n-1,...,n *)
fun NGOALS _ 0 _ st = all_tac st
  | NGOALS i n tac st = (tac (i+n-1) THEN NGOALS i (n-1) tac) st

fun some _ (SOME x) = x : thm
  | some procthms NONE = 
     let val pat = #pattern procthms 
         val ppat = Syntax.pretty_term_global (Thm.theory_of_cterm pat) (Thm.term_of pat) |> Pretty.string_of
     in
     error ("Could not access body etc. of "^ppat)
     end

val callproc_rule_conditions_tac_simpset =
  let val subgoaler_ss = 
            (put_simpset HOL_basic_ss @{context})
              addsimps @{thms List.list.inject String.char.inject String.nibble.distinct HOL.simp_thms}
            |> Raw_Simplifier.simpset_of
  in
  (put_simpset HOL_basic_ss @{context})
    addsimps @{thms callproc_conditions_simp.filter_global' callproc_conditions_simp.filter_global'_cons1 callproc_conditions_simp.filter_global'_cons2
  callproc_conditions_simp.filter_global'_nil callproc_conditions_simp.filter_local_union callproc_conditions_simp.filter_local' vars_variable_pattern[THEN eq_reflection]
  callproc_conditions_simp.filter_local'_cons1 callproc_conditions_simp.filter_local'_cons2 callproc_conditions_simp.filter_local'_nil callproc_conditions_simp.filter_local_insert1
  callproc_conditions_simp.filter_local_empty callproc_conditions_simp.local_variable_name_renaming_insert callproc_conditions_simp.local_variable_name_renaming_union
  callproc_conditions_simp.local_variable_name_renaming_nil callproc_conditions_simp.local_variable_name_renaming_same image_empty[THEN eq_reflection]
  vars_unit_pattern[THEN eq_reflection] vars_pair_pattern[THEN eq_reflection] 
  append_Cons[THEN eq_reflection] append_Nil[THEN eq_reflection]
  rename_local_variables_pattern_id[THEN eq_reflection] callproc_conditions_simp.local_variable_name_renaming_id
  callproc_conditions_simp.local_variable_name_renaming_set callproc_conditions_simp.local_variable_name_renaming_cons 
  callproc_conditions_simp.local_variable_name_renaming_nil2 callproc_conditions_simp.local_variable_name_renaming_notsame
  callproc_conditions_simp.filter_local_insert2
  }
  |> Simplifier.set_subgoaler (fn ctx => (@{print} "init_subgoaler"; simp_tac (put_simpset subgoaler_ss ctx)))
  |> Raw_Simplifier.simpset_of
  end;;

(* If the number of precondition of "callproc_rule" changed, need to change the number after NGOALS accordingly.
   callproc_rule_conditions_tac is supposed to solve all subgoals of "callproc_rule" except the last one. *) 
fun callproc_rule_conditions_tac ctx (procthms:Procs_Typed.procedure_info) i =
  let (*val simp = Raw_Simplifier.rewrite_goal_tac ctx 
         ([#body_local_vars procthms |> some procthms, 
           #return_vars procthms |> some procthms, 
           #args procthms |> some procthms] @ 
         @{thms callproc_conditions_simp.callproc_conditions_simp})*)
      val _ = @{print} "callproc_rule_conditions_tac"
      val simpset = (put_simpset callproc_rule_conditions_tac_simpset ctx)
            addsimps [#body_local_vars procthms |> some procthms, 
                      #return_vars procthms |> some procthms, 
                      #args procthms |> some procthms]
  in
  NGOALS i 6 (fn i =>
    if i=4 then ASSERT_SUCCESS' (solve_tac ctx @{thms callproc_conditions_simp.callproc_goal4})
                  (fn t => TERM("callproc_rule_conditions_tac, goal 4", [t])) 4
    else
      simp_tac simpset i
      (* THEN print_tac ctx ("condition "^string_of_int i) *)
      (* TODO: what is the fasted tactic for set equalities? *)
      THEN (ASSERT_SOLVED' (simp_tac ctx) 
         (fn _ => fn subgoals => raise TERM("callproc_rule_conditions_tac, goal "^string_of_int i,[nth subgoals (i-1)])) i))
  end

fun callproc_rule_tac' ctx (procthms:Procs_Typed.procedure_info) renaming locals non_parg_locals i =
  let val callproc_rule = @{thm callproc_rule_renamed} |> Thm.instantiate' []
        [SOME (Thm.cterm_of ctx renaming), NONE, SOME (Thm.cterm_of ctx locals), NONE, NONE, NONE, SOME (Thm.cterm_of ctx non_parg_locals)]
(*       val simp_rules = @{thms vars_variable_pattern[THEN eq_reflection] 
        assign_default_typed_aux[THEN eq_reflection] assign_default_typed_aux_cons[THEN eq_reflection]
        assign_default_typed_aux_nil[THEN eq_reflection]} *) 
  in resolve_tac ctx [callproc_rule] i
     (* THEN print_tac ctx "callproc_rule subgoals" *)
     THEN callproc_rule_conditions_tac ctx procthms i
     (* THEN print_tac ctx "conditions done" *)
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#args procthms |> some procthms] i
(*     THEN print_tac ctx "step1"*)
     (* THEN Raw_Simplifier.rewrite_goal_tac ctx simp_rules i *)
(*     THEN print_tac ctx "step2"*)
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#return procthms |> some procthms] i
(*     THEN print_tac ctx "step3"*)
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#body procthms |> some procthms] i
(*     THEN print_tac ctx "step4"*)
  end

fun procedure_local_vars ctx proc (procthms:Procs_Typed.procedure_info) =
  let fun extr1 args (Const(@{const_name variable_pattern},_) $ v) =
            (case v of (Const(@{const_name LVariable},_)$_) => [@{termx "mk_variable_untyped (?v::?'w::prog_type variable)" where "?'v.1\<Rightarrow>?'w variable"}]
                     | (Const(@{const_name Variable},_)$_) => [] (* Drop global vars *)
                     | _ => raise TERM ("While trying to extract local variables from body/return-expression of procedure (1), got the expression (2), which contains the unexpected term (3).\n" ^
                                        "Probably you need to add additional lemmas to 'procedure_info' to rewrite term (3)",
                                        [proc,args,v]))
        | extr1 _ (Const(@{const_name unit_pattern},_)) = []
        | extr1 args (Const(@{const_name pair_pattern},_) $ a $ b) = extr1 args a @ extr1 args b
        | extr1 args t = raise TERM ("While trying to extract variables from the arguments of procedure (1), got the expression (2), which contains the unexpected term (3).\n" ^
                                     "Probably you need to add additional lemmas to 'procedure_info' to rewrite term (3)",
                                     [proc,args,t])
      fun some (SOME x) = x 
        | some NONE = error ("procedure_local_vars: body of "^Pretty.string_of (Syntax.pretty_term ctx proc)^" not known")
      fun extr2 _ (Const(@{const_name Orderings.bot_class.bot},_)) = []
        | extr2 fullterm (Const(@{const_name Set.insert},_) $ v $ rest) =
            (case v of Const(@{const_name mk_variable_untyped},_) $ (Const(@{const_name LVariable},_)$_) => v :: extr2 fullterm rest
                     | Const(@{const_name mk_variable_untyped},_) $ (Const(@{const_name Variable},_)$_) => extr2 fullterm rest (* Drop global vars *)
                     | _ => raise TERM ("While trying to extract local variables from body/return-expression of procedure (1), got the expression (2), which contains the unexpected term (3).\n" ^
                                        "Probably you need to add additional lemmas to 'procedure_info' to rewrite term (3)",
                                        [proc,fullterm,v]))
        | extr2 fullterm (Const(@{const_name sup},_) $ a $ b) = extr2 fullterm a @ extr2 fullterm b
        | extr2 fullterm t = raise TERM ("While trying to extract local variables from body/return-expression of procedure (1), got the expression (2), which contains the unexpected term (3).\n" ^
                                         "Probably you need to add additional lemmas to 'procedure_info' to rewrite term (3)",
                                         [proc,fullterm,t])
      val args = #args procthms |> some |> Thm.rhs_of |> Thm.term_of |> (fn t => extr1 t t)
      val body_vars = #body_local_vars procthms |> some |> Thm.rhs_of |> Thm.term_of |> (fn t => extr2 t t)
      val return_vars = #return_vars procthms |> some |> Thm.rhs_of |> Thm.term_of |> (fn t => extr2 t t)
      val local_vars = args @ body_vars @ return_vars |> distinct (op aconv)
      val non_parg_locals = subtract (op aconv) args local_vars
   in (local_vars,non_parg_locals) end


fun make_renaming (_:Proof.context) to_rename dont_use : (string*string) list * term =
  let fun var_to_name (Const(@{const_name mk_variable_untyped},_) $ (Const(@{const_name Variable},_) $ _)) = NONE
        | var_to_name (v as Const(@{const_name mk_variable_untyped},_) $ (Const(@{const_name LVariable},_) $ n)) =
            (SOME (HOLogic.dest_string n) handle TERM _ => raise (TERM ("Variable name is not a string",[v,n])))
        | var_to_name v = raise (TERM ("Expecting a variable (mk_variable_untyped ([L]Variable str))",[v]))
      val to_rename = map_filter var_to_name to_rename
      val dont_use = map_filter var_to_name dont_use
      val to_rename = distinct (op=) to_rename
      val newnames = Name.variant_list dont_use to_rename
      val renaming = ListPair.zip (to_rename, newnames)
      val renaming_term = renaming |> map (fn (x,y) => HOLogic.mk_prod (HOLogic.mk_string x, HOLogic.mk_string y))
                                   |> HOLogic.mk_list @{typ "string * string"}
(* val _ = writeln (Syntax.string_of_term ctx renaming_term) *)
  in
    (renaming,renaming_term)
  end

(* This assumes a renaming that has no overlapping transposition *)
(*fun apply_local_var_renaming (_:Proof.context) renaming var =
  let val f = AList.lookup (op=) renaming
      fun ren (v as Const(@{const_name mk_variable_untyped},_) $ (Const(@{const_name Variable},_) $ _)) = v
        | ren (v as (c1 as Const(@{const_name mk_variable_untyped},_)) $ ((c2 as Const(@{const_name LVariable},_)) $ n)) =
            (case f (HOLogic.dest_string n) of
              SOME n' => c1 $ (c2 $ HOLogic.mk_string n')
            | NONE => v)
            handle TERM _ => raise (TERM ("Variable name is not a string",[v,n]))
  in
    ren var
  end*)
fun apply_local_var_renaming (_:Proof.context) renaming var = 
  let fun ren1 _ (v as Const(@{const_name mk_variable_untyped},_) $ (Const(@{const_name Variable},_) $ _)) = v
        | ren1 (a,b) (v as (c1 as Const(@{const_name mk_variable_untyped},_)) $ ((c2 as Const(@{const_name LVariable},_)) $ n)) =
            (let val n' = HOLogic.dest_string n in
              if n'=a then c1 $ (c2 $ HOLogic.mk_string b)
              else if n'=b then c1 $ (c2 $ HOLogic.mk_string a)
              else v
            end handle TERM _ => raise (TERM ("Variable name is not a string",[v,n])))
        | ren1 _ v = raise (TERM ("Expecting a variable (mk_variable_untyped ([L]Variable str))",[v]))
  in
  fold ren1 renaming var
  end

(*
(* Transforms a goal of the form
     "obs_eq' V (callproc x proc args) ?body"
   where ?body is instantiated to be the unfolding of the procedure call
   into
     "obs_eq' V (callproc x (rename_local_variables_proc ren proc) args) ?body"
   where ren is a renaming that renames the local variables "to_rename" into fresh names, avoiding the names in "dont_use".

   Duplicates in to_rename and dont_use are silently ignored
*)
fun obs_eq'_rename_variables_proc _ [] _ = all_tac
  | obs_eq'_rename_variables_proc ctx to_rename dont_use =
  let fun var_to_name (Const(@{const_name mk_variable_untyped},_) $ (Const(@{const_name Variable},_) $ _)) = NONE
        | var_to_name (v as Const(@{const_name mk_variable_untyped},_) $ (Const(@{const_name LVariable},_) $ n)) =
            SOME (HOLogic.dest_string n) handle TERM _ => raise (TERM ("Variable name is not a string",[v,n]))
      val to_rename = map_filter var_to_name to_rename
      val dont_use = map_filter var_to_name dont_use
      val to_rename = distinct (op=) to_rename
      val newnames = Name.variant_list dont_use to_rename
      val renaming = ListPair.zip (to_rename, newnames)
      val renaming_term = renaming |> map (fn (x,y) => HOLogic.mk_prod (HOLogic.mk_string x, HOLogic.mk_string y))
                                   |> HOLogic.mk_list @{typ "string * string"}
val _ = writeln (Syntax.string_of_term ctx renaming_term)
  in
  (* TODO: use rule obs_eq'_rename_variables_proc[of _ _ renaming_term] *)
  resolve_tac ctx (Drule.instantiate' [] [NONE, NONE, SOME (Thm.cterm_of ctx renaming_term)] @{thm obs_eq'_rename_variables_proc}) 1
  end
*)

(* Solves a goal of the form
     "obs_eq' V (callproc x proc args) ?body"
   where ?body is instantiated to be the unfolding of the procedure call.

   It is roughly equivalent to: 
     ML_prf {* val procthms = Tactic_Inline.procedure_get_thms @{context} facts true proc *} (* Obtain info about proc *)
                                                                                             (* Try "false" instead of "true" to see where it gets stuck *)
     ML_prf {* val locals = Tactic_Inline.procedure_local_vars proc procthms |> fst |> HOLogic.mk_list @{typ variable_untyped} *} (* Obtain local variables of proc *)
     ML_prf {* val non_parg_locals = Tactic_Inline.procedure_local_vars proc procthms |> snd |> HOLogic.mk_list @{typ variable_untyped} *} (* Obtain non-arg local variables of proc *)
     apply (tactic \<open>Tactic_Inline.callproc_rule_tac' @{context} procthms locals non_parg_locals 1\<close>)
   Here "locals:term" is a HOL-list of the local variables occuring in the procedure proc.
   And "non_parg_locals" is a HOL-list containing the locals, without the variables occurring in the procedure argument list.

   "forbidden" lists local variables that must not occur in ?body 
   (currently, no renaming is performed, the method fails if proc has local variables in "forbidden")
*)
(* NOTE: facts are not currently used! *)
fun callproc_rule_tac ctx _ forbidden = 
  SUBGOAL (fn (goal,i) =>
  let val proc = case Logic.strip_assums_concl goal of
        Const(@{const_name Trueprop},_) $ 
             (Const(@{const_name obs_eq'},_) $ _ $ (Const(@{const_name callproc},_)$_$p$_) $ _) => p
         | t => raise TERM("callproc_rule_tac: goal is not of the form ??? (TODO)",[t])
      val procthms = (*procedure_get_thms ctx facts false proc*) 
                     Procs_Typed.get_procedure_info ctx false proc
      val (locals,non_parg_locals) = procedure_local_vars ctx proc procthms
      val forbidden_inter = inter (fn (x,y) => (map_types (K dummyT) x) aconv (map_types (K dummyT) y)) locals forbidden
      val (renaming,renaming_term) = make_renaming ctx forbidden_inter (forbidden@locals)
(*       val _ = if forbidden_inter = [] then () else
        raise TERM("callproc_rule_tac: locals (2) and forbidden vars (3) have nonempty intersection (1)",
                   [forbidden_inter |> HOLogic.mk_list @{typ variable_untyped},
                    locals |> HOLogic.mk_list @{typ variable_untyped},
                    forbidden |> HOLogic.mk_list @{typ variable_untyped}]) *)
      val locals' = HOLogic.mk_list @{typ variable_untyped} (map (apply_local_var_renaming ctx renaming) locals)
      val non_parg_locals = HOLogic.mk_list @{typ variable_untyped} (map (apply_local_var_renaming ctx renaming) non_parg_locals)
  in
(*    obs_eq'_rename_variables_proc ctx forbidden_inter (forbidden@locals)
    THEN
    (* TODO: callproc_rule_tac' needs renamed procthms, locals' non_parg_locals *) *)
    callproc_rule_tac' ctx procthms renaming_term locals' non_parg_locals i
  end)

(* TODO use a more efficient data structure than lists for collecting variables *)
fun program_local_vars' (Const(@{const_name seq},_) $ p1 $ p2) = program_local_vars' p1 @ program_local_vars' p2
  | program_local_vars' (Const(@{const_name program},_) $ p) = program_local_vars' p
  | program_local_vars' (Const(@{const_name assign},_) $ v $ e) = pattern_local_vars' v @ expression_local_vars' e
  | program_local_vars' (Const(@{const_name sample},_) $ v $ e) = pattern_local_vars' v @ expression_local_vars' e
  | program_local_vars' (Const(@{const_name callproc},_) $ x $ _ $ a) = pattern_local_vars' x @ expression_local_vars' a
  | program_local_vars' (Const(@{const_name skip},_)) = []
  | program_local_vars' t = raise TERM("INTERNAL ERROR: program_local_vars: not implemented",[t])
and var_if_local' (v as Const(@{const_name LVariable},_)$_) = [v]
  | var_if_local' (Const(@{const_name Variable},_)$_) = []
  | var_if_local' t = raise TERM("program_local_vars",[t])
and expression_local_vars' (Const(@{const_name apply_expression},_)$e$v) = var_if_local' v @ expression_local_vars' e
  | expression_local_vars' (Const(@{const_name const_expression},_)$_) = []
  | expression_local_vars' t = raise TERM("program_local_vars\<rightarrow>expression",[t])
and pattern_local_vars' (Const(@{const_name variable_pattern},_)$v) = var_if_local' v
  | pattern_local_vars' (Const(@{const_name pair_pattern},_) $ p1 $ p2) =
      pattern_local_vars' p1 @ pattern_local_vars' p2
  | pattern_local_vars' (Const(@{const_name unit_pattern},_)) = []
  | pattern_local_vars' t = raise TERM("program_local_vars\<rightarrow>pattern",[t])

fun program_local_vars t = program_local_vars' t |> distinct (op aconv)
fun program_local_vars_untyped t = program_local_vars t |> map (fn v =>
  @{termx "mk_variable_untyped (?v::?'w::prog_type variable)" where "?'v.1\<Rightarrow>?'w variable"})

fun contains_pattern ctx pattern term =
  let val thy = Proof_Context.theory_of ctx
      fun match t : bool = (Pattern.first_order_match thy (pattern,t) (Vartab.empty, Vartab.empty); true)
                           handle Pattern.MATCH => false
  in
    Term.exists_subterm match term
  end


(* Given a subgoal of the form
   G := "hoare {P} p1 {Q}" or "hoare {P} p1 ~ p2 {Q}"
   such that a subterm of p1 or p2 matches the pattern "redex",
   transform it into the goals:

   * obseq_context X C   // where C is the context of p1/p2 around the match for "redex"
   * assertion_footprint X Q   // for suitable X Q
   * obs_eq' X c ?d    // where c is the subterm of p1/p2 matching redex
   * G with c replaced by ?d 
*)
fun hoare_obseq_replace_tac ctx redex obseq_tac =
  SUBGOAL (fn (goal,i) =>
  let 
(*      fun hoare_obseq_replace vars redex = @{thm hoare_obseq_replace} |> Drule.instantiate' [] [SOME vars(*X*),NONE,NONE,SOME redex(*c*)]
      fun rhoare_obseq_replace_left vars redex = @{thm rhoare_left_obseq_replace} |> Drule.instantiate' [] [SOME vars(*X*),NONE,NONE,SOME redex(*c*)]*)
      val concl = Logic.strip_assums_concl goal
      val (obseq_rule,program) = case concl of @{termx "Trueprop (Hoare_Typed.hoare ?P ?c ?Q)"} => 
                                                 let val _ = (P,Q) (* Avoids ML warning *)
                                                     val _ = if contains_pattern ctx redex c then () else raise TERM("hoare_obseq_replace_tac: Hoare triple does not contain pattern",[concl,redex])
                                                 in (@{thm hoare_obseq_replace_ctx},c) end
                                             | @{termx "Trueprop (rhoare ?P ?c ?c' ?Q)"} => 
                                                 if contains_pattern ctx redex c then (@{thm rhoare_left_obseq_replace},c)
                                                 else if contains_pattern ctx redex c' then (@{thm rhoare_right_obseq_replace},c')
                                                 else raise K (TERM("hoare_obseq_replace_tac: RHL tuple (1) does not contain pattern (2)",[concl,redex])) (P,Q)
                                             | t => raise TERM("hoare_obseq_replace_tac: goal not a Hoare tuple",[t])
      val program_locals = program_local_vars_untyped program
      val program_locals_set = program_locals |> HOLogic.mk_set @{typ variable_untyped} 
      val obs_eq_vars = @{termx "?program_locals_set \<union> Collect (vu_global::variable_untyped\<Rightarrow>_)"} |> Thm.cterm_of ctx
      val redex = Thm.cterm_of ctx redex
      val obseq_rule = obseq_rule |> Thm.instantiate' [] [SOME obs_eq_vars(*X*),NONE,NONE,SOME redex(*c*)]
  in
    ASSERT_SUCCESS (resolve_tac ctx [obseq_rule] i) (THM("Could not apply hoare_obseq_replace",i,[obseq_rule]))
    THEN ASSERT_SOLVED' (fast_force_tac (ctx addSIs @{thms obseq_context_empty obseq_context_seq obseq_context_assign obseq_context_sample  obseq_context_ifte obseq_context_while obseq_context_skip obseq_context_callproc_allglobals}))
         (fn subgoal1 => fn subgoals => raise TERM("While trying to prove (1) using hoare_obseq_replace, I got subgoal (2).\n"^
                                                   "I could not prove that subgoal using 'fastforce obseq_context_empty obseq_context_seq obseq_context_assign obseq_context_sample obseq_context_ifte obseq_context_while obseq_context_skip obseq_context_callproc_allglobals'.\n",
                                                   goal::subgoal1::subgoals)) i
(*    THEN ASSERT_SUCCESS (Raw_Simplifier.rewrite_goal_tac ctx @{thms assertion_footprint_def memory_lookup_def} i)
         (ERROR "Internal error: Raw_Simplifier.rewrite_goal_tac failed") *)
    THEN ASSERT_SOLVED' (assertion_footprint_tac ctx THEN_ALL_NEW simp_tac ctx)
         (fn goal => fn subgoals => raise TERM("Could not solve second subgoal of hoare_obseq_replace",goal::subgoals)) i
    THEN (case obseq_tac of NONE => all_tac
          | SOME tac => ASSERT_SUCCESS (tac program_locals i)
                        (ERROR "obseq_tac failed"))
  end)

(* Simpset that does the following simplifications:

1. simplifies away occurrences of rename_local_variables
*)  
val after_inline_simpset =
  let val subgoaler_ss = 
            (put_simpset HOL_basic_ss @{context})
              addsimps @{thms List.list.inject String.char.inject String.nibble.distinct HOL.simp_thms}
            |> Raw_Simplifier.simpset_of
  in
  (put_simpset HOL_basic_ss @{context})
    addsimps @{thms 
Lang_Typed.rename_local_variables_variable_pattern
Lang_Typed.rename_local_variables_var_id
Lang_Typed.rename_local_variables_seq
Lang_Typed.rename_local_variables_sample
Lang_Typed.rename_local_variables_assign
Lang_Typed.rename_local_variables_callproc
Lang_Typed.rename_local_variables_pair_pattern
Lang_Typed.rename_local_variables_unit_pattern
Lang_Typed.rename_local_variables_const_expression
Lang_Typed.rename_local_variables_apply_expression
rename_local_variables_var_same
rename_local_variables_var_notsame
rename_local_variables_var_global
vars_variable_pattern[THEN eq_reflection] 
assign_default_typed_aux[THEN eq_reflection] assign_default_typed_aux_cons[THEN eq_reflection]
assign_default_typed_aux_nil[THEN eq_reflection]
}
  |> Simplifier.set_subgoaler (fn ctx => (@{print} "init_subgoaler"; simp_tac (put_simpset subgoaler_ss ctx)))
  |> Raw_Simplifier.simpset_of
  end;;


(* Inlines the procedure "proc" (one occurrence only) in the current goal.

  It is roughly equivalent to: 

    apply (tactic \<open>Tactic_Inline.hoare_obseq_replace_tac @{context} @{term "callproc ?x proc ?a"} NONE 1\<close>)
    apply (tactic \<open>Tactic_Inline.callproc_rule_tac @{context} facts locals 1\<close>)

  where "locals:term list" is the list of all local variables in the current goal (each of the form "mk_variable_untyped (LVariable ''x''::type)").
  (that list is also contained in the goal produced by Tactic_Inline.hoare_obseq_replace_tac)
*)
fun inline_tac ctx facts proc =
  SUBGOAL (fn (goal,i) =>
    (* TODO: make sure there are no collisions of schematic variables between pattern and
        (proc and all goals) *)
    let val idx = maxidx_of_term goal + 1
        val (aT,bT) = case fastype_of proc of
              Type(@{type_name procedure_ext},[aT,bT,@{typ unit}]) => (aT,bT)
              | T => raise TYPE("inline_tac expects procedure of type (_,_)procedure",[T],[proc])
        val pattern = 
            @{termx "callproc::_\<Rightarrow>(?'aT::prog_type,?'bT::prog_type)procedure\<Rightarrow>_\<Rightarrow>_"} $
              Var(("_x",idx),@{typx "?'bT pattern"}) $
              proc $
              Var(("_a",idx),@{typx "?'aT expression"})
        (* val pattern = Drule.instantiate' [] [] callproc_pattern *)
        val callproc = callproc_rule_tac ctx facts
        val obseq = hoare_obseq_replace_tac ctx pattern (SOME callproc) i
        val simp = simp_tac (put_simpset after_inline_simpset ctx) i
     in obseq THEN simp end)

end
