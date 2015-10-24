structure Tactic_Inline =
struct

fun has_Bound0 t =
  let fun h (Bound i) j = i=j
        | h (Free _) _ = false
        | h (Var _) _ = false
        | h (a$b) i = h a i orelse h b i
        | h (Abs(_,_,t)) i = h t (i+1)
        | h (Const _) _ = false
  in h t 0 end

fun assertion_footprint_tac ctx = SUBGOAL (fn (goal,i) =>
  case goal of
    Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint},_) $ X $ (Abs(v,T,t))) => 
      if not (has_Bound0 t) then solve_tac ctx @{thms assertion_footprint_const} i
      else (case t of
             Const(@{const_name memory_lookup},_) $ Bound 0 $ _ =>
               rtac @{thm assertion_footprint_lookup} i
           | t1 $ t2 => 
                let val ct1 = Abs(v,T,t1) |> Thm.cterm_of ctx
                    val ct2 = Abs(v,T,t2) |> Thm.cterm_of ctx
                    val ctX = X |> Thm.cterm_of ctx
                    val cts = Thm.ctyp_of_cterm ct1 |> Thm.dest_ctyp |> (fn x => nth x 1) |> Thm.dest_ctyp
                in
                  (rtac (Drule.instantiate' [SOME (hd cts), SOME (hd (tl cts))] [SOME ctX,SOME ct1,SOME ct2]
                    @{thm assertion_footprint_app}) THEN_ALL_NEW assertion_footprint_tac ctx) i
                end
           | _ => raise (TERM( "nyi",[t])))
  | Const(@{const_name Trueprop},_) $ (Const(@{const_name assertion_footprint},_) $ _ $ _) => 
    raise (TERM ("handle this case!", [goal]))
  | _ => raise (TERM ("write real error message", [goal])))


datatype no_return = NoReturn of no_return

fun string_of_varlist ctx vs =
  (String.concatWith "\n" 
  (map (fn t => case t of _$v => Syntax.string_of_term ctx t ^ " (" ^ Syntax.string_of_typ ctx (fastype_of v) ^ ")"
                        | _ => Syntax.string_of_term ctx t)  vs))

fun ASSERT_SUCCESS (tac:tactic) exn st = 
  let val res = tac st 
      val _ = case Seq.pull res of NONE => raise exn | _ => ()
  in res end
fun ASSERT_SUCCESS' (tac:int->tactic) (exn:term->exn) = 
  SUBGOAL (fn (goal,i) => fn st =>
  let val res = tac i st
      val _ = case Seq.pull res of NONE => raise (exn goal) | _ => ()
  in res end)
fun ASSERT_SOLVED' (tac:int->tactic) (exn:term->term list->no_return) = 
  SUBGOAL (fn (goal,i) => fn st =>
  let val res = tac i st
      val solved = Seq.filter (fn st' => Thm.nprems_of st' < Thm.nprems_of st) res
      val _ = case (Seq.pull res, Seq.pull solved) of
                (_,SOME _) => ()
              | (NONE,NONE) => (exn goal []; raise ERROR "impossible")
              | (SOME(st',_),NONE) => (exn goal (Thm.prems_of st'); raise ERROR "impossible")
  in res end)

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
    addsimps @{thms callproc_conditions_simp.callproc_conditions_simp}
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
      THEN (ASSERT_SUCCESS' (simp_tac ctx) (fn t => TERM("callproc_rule_conditions_tac, goal "^string_of_int i, [t])) i))
  end

fun callproc_rule_tac' ctx (procthms:Procs_Typed.procedure_info) renaming locals non_parg_locals i =
  let val callproc_rule = @{thm callproc_rule_renamed} |> Drule.instantiate' []
        [SOME (Thm.cterm_of ctx renaming), NONE, SOME (Thm.cterm_of ctx locals), NONE, NONE, NONE, SOME (Thm.cterm_of ctx non_parg_locals)]
      val simp_rules = @{thms vars_variable_pattern[THEN eq_reflection] 
        assign_default_typed_aux[THEN eq_reflection] assign_default_typed_aux_cons[THEN eq_reflection]
        assign_default_typed_aux_nil[THEN eq_reflection]} 
  in rtac callproc_rule i
     (* THEN print_tac ctx "callproc_rule subgoals" *)
     THEN callproc_rule_conditions_tac ctx procthms i
     (* THEN print_tac ctx "conditions done" *)
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#args procthms |> some procthms] i
(*     THEN print_tac ctx "step1"*)
     THEN Raw_Simplifier.rewrite_goal_tac ctx simp_rules i
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


fun make_renaming ctx to_rename dont_use : (string*string) list * term =
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
    (renaming,renaming_term)
  end

(* This assumes a renaming that has no overlapping transposition *)
fun apply_local_var_renaming ctx renaming var =
  let val f = AList.lookup (op=) renaming
      fun ren (v as Const(@{const_name mk_variable_untyped},_) $ (Const(@{const_name Variable},_) $ _)) = v
        | ren (v as (c1 as Const(@{const_name mk_variable_untyped},_)) $ ((c2 as Const(@{const_name LVariable},_)) $ n)) =
            (case f (HOLogic.dest_string n) of
              SOME n' => c1 $ (c2 $ HOLogic.mk_string n')
            | NONE => v)
            handle TERM _ => raise (TERM ("Variable name is not a string",[v,n]))
  in
    ren var
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
  rtac (Drule.instantiate' [] [NONE, NONE, SOME (Thm.cterm_of ctx renaming_term)] @{thm obs_eq'_rename_variables_proc}) 1
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



fun hoare_obseq_replace_tac ctx redex obseq_tac =
  SUBGOAL (fn (goal,i) =>
  let 
      val concl = Logic.strip_assums_concl goal
      val program = case concl of @{termx "Trueprop (Hoare_Typed.hoare ?P ?c ?Q)"} => K c (P,Q)
                                | t => raise TERM("hoare_obseq_replace_tac: goal not a Hoare triple",[t])
      val program_locals = program_local_vars_untyped program
      val program_locals_set = program_locals |> HOLogic.mk_set @{typ variable_untyped} 
      val obs_eq_vars = @{termx "?program_locals_set \<union> Collect (vu_global::variable_untyped\<Rightarrow>_)"} |> Thm.cterm_of ctx
      val redex = Thm.cterm_of ctx redex
      val obseq_rule = @{thm hoare_obseq_replace} |> Drule.instantiate' [] [SOME obs_eq_vars(*X*),NONE,NONE,SOME redex(*c*)]
  in
    ASSERT_SUCCESS (rtac obseq_rule i) (THM("Could not apply hoare_obseq_replace",i,[obseq_rule]))
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
