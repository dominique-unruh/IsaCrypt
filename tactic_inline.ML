structure Tactic_Inline =
struct

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

(* If the number of precondition of "callproc_rule" changed, need to change the number after NGOALS accordingly.
   callproc_rule_conditions_tac is supposed to solve all subgoals of "callproc_rule" except the last one. *) 
fun callproc_rule_conditions_tac ctx (procthms:Procs_Typed.procedure_info) i =
  NGOALS i 6 (fn i =>
  Raw_Simplifier.rewrite_goal_tac ctx
        [#body_local_vars procthms |> some procthms, 
         #return_vars procthms |> some procthms, 
         #args procthms |> some procthms] i
    THEN (fast_force_tac ctx i))

fun callproc_rule_tac' ctx (procthms:Procs_Typed.procedure_info) locals non_parg_locals i =
  let val callproc_rule = @{thm callproc_rule} |> Drule.instantiate' []
        [NONE, SOME (Thm.cterm_of ctx locals), NONE, NONE, NONE, SOME (Thm.cterm_of ctx non_parg_locals)]
val _ = (writeln "locals"; writeln (Syntax.string_of_term ctx locals) )
val _ = (writeln "non_parg_locals"; writeln (Syntax.string_of_term ctx non_parg_locals) )
val _ = writeln (Display.string_of_thm ctx callproc_rule)
      val simp_rules = @{thms vars_variable_pattern[THEN eq_reflection] } (* TODO *)
  in rtac callproc_rule i
     (* THEN print_tac ctx "callproc_rule subgoals" *)
     THEN callproc_rule_conditions_tac ctx procthms i
     THEN print_tac ctx "conditions done"
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
      val _ = if inter (op aconv) locals forbidden = [] then () else
        raise TERM("callproc_rule_tac: locals and forbidden vars have nonempty intersection",
                   [locals |> HOLogic.mk_list @{typ variable_untyped},
                    forbidden |> HOLogic.mk_list @{typ variable_untyped}])
      val locals = HOLogic.mk_list @{typ variable_untyped} locals
      val non_parg_locals = HOLogic.mk_list @{typ variable_untyped} non_parg_locals
  in
    callproc_rule_tac' ctx procthms locals non_parg_locals i
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
(*and procargs_local_vars' (Const(@{const_name procargs_add},_)$e$a) = expression_local_vars' e @ procargs_local_vars' a
  | procargs_local_vars' (Const(@{const_name procargs_empty},_)) = []
  | procargs_local_vars' t = raise TERM("program_local_vars\<rightarrow>callproc args",[t])*)
and pattern_local_vars' (Const(@{const_name variable_pattern},_)$v) = var_if_local' v
  | pattern_local_vars' (Const(@{const_name pair_pattern},_) $ p1 $ p2) =
      pattern_local_vars' p1 @ pattern_local_vars' p2
  | pattern_local_vars' (Const(@{const_name unit_pattern},_)) = []
  | pattern_local_vars' t = raise TERM("program_local_vars\<rightarrow>pattern",[t]) (* TODO *)

fun program_local_vars t = program_local_vars' t |> distinct (op aconv)
fun program_local_vars_untyped t = program_local_vars t |> map (fn v =>
  @{termx "mk_variable_untyped (?v::?'w::prog_type variable)" where "?'v.1\<Rightarrow>?'w variable"})

datatype no_return = NoReturn of no_return

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
    THEN ASSERT_SUCCESS (Raw_Simplifier.rewrite_goal_tac ctx @{thms assertion_footprint_def memory_lookup_def} i)
         (ERROR "Internal error: Raw_Simplifier.rewrite_goal_tac failed")
    THEN ASSERT_SOLVED' (fast_force_tac ctx)
         (fn goal => fn subgoals => raise TERM("Could not solve second subgoal of hoare_obseq_replace",goal::subgoals)) i
    THEN (case obseq_tac of NONE => all_tac
          | SOME tac => ASSERT_SUCCESS (tac program_locals i)
                        (ERROR "obseq_tac failed"))
  end)

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
     in obseq end)

end
