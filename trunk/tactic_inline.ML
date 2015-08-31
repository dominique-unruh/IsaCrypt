structure Tactic_Inline =
struct

fun procedure_get_info_tac ctx localfacts partial =
  let 
      val facts = Proof_Context.get_fact ctx (Facts.named "procedure_info")
      val allfacts = localfacts@facts
      fun tac i = DETERM ((resolve0_tac allfacts THEN_ALL_NEW tac) i)
                  ORELSE (if partial then SOLVED' (resolve0_tac @{thms reflexive refl}) i else no_tac)
  in
  Raw_Simplifier.rewrite_goal_tac ctx localfacts 1
  THEN
  tac 1
  end

(*
fun procedure_get_info_tac ctx localfacts partial : tactic =
  let val facts = Proof_Context.get_fact ctx (Facts.named "procedure_info")
      val simpset = put_simpset HOL_basic_ss ctx 
                    addsimps localfacts
                    addsimps facts
      fun remove_HIDDEN_EQ_tac i = 
        ((fn i => resolve0_tac @{thms HIDDEN_EQ_ok} i THEN print_tac ctx "XXX") THEN_ALL_NEW remove_HIDDEN_EQ_tac) i
      val remove_HIDDEN_EQ_tac_partial = rtac @{thm HIDDEN_EQ_refl}
  in
  rtac @{thm HIDDEN_EQ_I'} 1
  THEN simp_tac simpset 1
  THEN print_tac ctx "final"
  THEN (if partial then SOLVED' remove_HIDDEN_EQ_tac_partial 1 else SOLVED' remove_HIDDEN_EQ_tac 1)
  end
*)

(* partial=false: enforce that the resulting theorem does not refer to info of subprocedures 
      (e.g., not "set (vars_proc_global (f g)) = {x} \union (set (vars_proc_global g))") *)
fun procedure_get_info ctx facts partial property : thm =
  let val goal = Logic.mk_equals (property, Var(("rhs",0),fastype_of property))
  in
  Goal.prove ctx [] [] goal (fn {context,prems} => procedure_get_info_tac context (prems@facts) partial)
  end

fun procedure_get_args ctx facts partial proc = 
  procedure_get_info ctx facts partial @{termx "p_args (?proc::?'proc.1)" where "?'proc.1 \<Rightarrow> (?'a::procargs, ?'b, ?'c) procedure_scheme"}
fun procedure_get_body ctx facts partial proc = 
  procedure_get_info ctx facts partial @{termx "p_body (?proc::?'proc.1)" where "?'proc.1 \<Rightarrow> (?'a::procargs, ?'b, ?'c) procedure_scheme"}
fun procedure_get_return ctx facts partial proc = 
  procedure_get_info ctx facts partial @{termx "p_return (?proc::?'proc.1)" where "?'proc.1 \<Rightarrow> (?'a::procargs, ?'b, ?'c) procedure_scheme"}
fun procedure_get_body_vars ctx facts partial proc =
  procedure_get_info ctx facts partial @{termx "set (vars (p_body (?proc::?'proc.1)))" where "?'proc.1 \<Rightarrow> (?'a::procargs, ?'b, ?'c) procedure_scheme"}
fun procedure_get_body_local_vars ctx facts partial proc =
  procedure_get_info ctx facts partial @{termx "set (local_vars (p_body (?proc::?'proc.1)))" where "?'proc.1 \<Rightarrow> (?'a::procargs, ?'b, ?'c) procedure_scheme"}
fun procedure_get_return_vars ctx facts partial proc =
  procedure_get_info ctx facts partial @{termx "set (e_vars (p_return (?proc::?'proc.1)))" where "?'proc.1 \<Rightarrow> (?'a::procargs, ?'b, ?'c) procedure_scheme"}

type procedure_thms = {args:thm, body:thm, return:thm, body_local_vars:thm, return_vars:thm}

fun procedure_get_thms ctx facts partial proc : procedure_thms = {
  args=procedure_get_args ctx facts partial proc,
  body=procedure_get_body ctx facts partial proc,
  return=procedure_get_return ctx facts partial proc,
  body_local_vars=procedure_get_body_local_vars ctx facts partial proc,
  return_vars=procedure_get_return_vars ctx facts partial proc
}

(* "NGOALS i n tac" applies tac to goals i+n-1,...,n *)
fun NGOALS _ 0 _ st = all_tac st
  | NGOALS i n tac st = (tac (i+n-1) THEN NGOALS i (n-1) tac) st

(* If the number of precondition of "callproc_rule" changed, need to change the number after NGOALS accordingly.
   callproc_rule_conditions_tac is supposed to solve all subgoals of "callproc_rule" except the last one. *) 
fun callproc_rule_conditions_tac ctx (procthms:procedure_thms) i =
  NGOALS i 9 (fn i =>
  Raw_Simplifier.rewrite_goal_tac ctx
        [#body_local_vars procthms, #return_vars procthms, #args procthms] i
    THEN (fast_force_tac ctx i))

fun callproc_rule_tac' ctx (procthms:procedure_thms) locals i =
  let val callproc_rule = @{thm callproc_rule} |> Drule.instantiate' [] [NONE, SOME (Thm.cterm_of ctx locals)]
      val simp_rules = @{thms assign_local_vars_typed_simp1[THEN eq_reflection] 
                         assign_local_vars_typed_simp2[THEN eq_reflection] assign_local_vars_typed_simp3[THEN eq_reflection]}
  in rtac callproc_rule i
     THEN callproc_rule_conditions_tac ctx procthms i
(*     THEN print_tac ctx "conditions done"*)
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#args procthms] i
(*     THEN print_tac ctx "step1"*)
     THEN Raw_Simplifier.rewrite_goal_tac ctx simp_rules i
(*     THEN print_tac ctx "step2"*)
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#return procthms] i
(*     THEN print_tac ctx "step3"*)
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#body procthms] i
(*     THEN print_tac ctx "step4"*)
  end

fun procedure_local_vars proc (procthms:procedure_thms) =
  let fun extr1 _ (Const(@{const_name procargvars_empty},_)) = []
        | extr1 args (Const(@{const_name procargvars_add},_) $ v $ rest) = 
            @{termx "mk_variable_untyped (?v::?'w::prog_type variable)" where "?'v.1\<Rightarrow>?'w variable"} :: extr1 args rest
        | extr1 args t = raise TERM ("While trying to extract variables from the arguments of procedure (1), got the expression (2), which contains the unexpected term (3).\n" ^
                                     "Probably you need to add additional lemmas to 'procedure_info' to rewrite term (3)",
                                     [proc,args,t])
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
      val args = Thm.rhs_of (#args procthms) |> Thm.term_of |> (fn t => extr1 t t)
      val body_vars = Thm.rhs_of (#body_local_vars procthms) |> Thm.term_of |> (fn t => extr2 t t)
      val return_vars = Thm.rhs_of (#return_vars procthms) |> Thm.term_of |> (fn t => extr2 t t)
      val local_vars = args @ body_vars @ return_vars |> distinct (op aconv)
   in local_vars end

(* Solves a goal of the form
     "obs_eq' V (callproc x proc args) ?body"
   where ?body is instantiated to be the unfolding of the procedure call.

   It is roughly equivalent to: 
     ML_prf {* val procthms = Tactic_Inline.procedure_get_thms @{context} facts true proc *} (* Obtain info about proc *)
                                                                                             (* Try "false" instead of "true" to see where it gets stuck *)
     ML_prf {* val locals = Tactic_Inline.procedure_local_vars proc procthms |> HOLogic.mk_list @{typ variable_untyped} *} (* Obtain local variables of proc *)
     apply (tactic \<open>Tactic_Inline.callproc_rule_tac' @{context} procthms locals 1\<close>)
   Here "locals:term" is a HOL-list of the local variables occuring in the procedure proc

   "forbidden" lists local variables that must not occur in ?body 
   (currently, no renaming is performed, the method fails if proc has local variables in "forbidden"   
*)
fun callproc_rule_tac ctx facts forbidden = 
  SUBGOAL (fn (goal,i) =>
  let val proc = case Logic.strip_assums_concl goal of
        Const(@{const_name Trueprop},_) $ 
             (Const(@{const_name obs_eq'},_) $ _ $ (Const(@{const_name callproc},_)$_$p$_) $ _) => p
         | t => raise TERM("callproc_rule_tac: goal is not of the form ??? (TODO)",[t])
      val procthms = procedure_get_thms ctx facts false proc
      val locals = procedure_local_vars proc procthms
      val _ = if inter (op aconv) locals forbidden = [] then () else
        raise TERM("callproc_rule_tac: locals and forbidden vars have nonempty intersection",
                   [locals |> HOLogic.mk_list @{typ variable_untyped},
                    forbidden |> HOLogic.mk_list @{typ variable_untyped}])
      val locals = HOLogic.mk_list @{typ variable_untyped} locals
  in
    callproc_rule_tac' ctx procthms locals i
  end)

(* TODO use a more efficient data structure than lists for collecting variables *)
fun program_local_vars' (Const(@{const_name seq},_) $ p1 $ p2) = program_local_vars' p1 @ program_local_vars' p2
  | program_local_vars' (Const(@{const_name program},_) $ p) = program_local_vars' p
  | program_local_vars' (Const(@{const_name assign},_) $ v $ e) = var_if_local' v @ expression_local_vars' e
  | program_local_vars' (Const(@{const_name sample},_) $ v $ e) = var_if_local' v @ expression_local_vars' e
  | program_local_vars' (Const(@{const_name callproc},_) $ x $ _ $ a) = var_if_local' x @ procargs_local_vars' a
  | program_local_vars' (Const(@{const_name skip},_)) = []
  | program_local_vars' t = raise TERM("INTERNAL ERROR: program_local_vars: not implemented",[t])
and var_if_local' (v as Const(@{const_name LVariable},_)$_) = [v]
  | var_if_local' (Const(@{const_name Variable},_)$_) = []
  | var_if_local' t = raise TERM("program_local_vars",[t])
and expression_local_vars' (Const(@{const_name apply_expression},_)$e$v) = var_if_local' v @ expression_local_vars' e
  | expression_local_vars' (Const(@{const_name const_expression},_)$_) = []
  | expression_local_vars' t = raise TERM("program_local_vars\<rightarrow>expression",[t])
and procargs_local_vars' (Const(@{const_name procargs_add},_)$e$a) = expression_local_vars' e @ procargs_local_vars' a
  | procargs_local_vars' (Const(@{const_name procargs_empty},_)) = []
  | procargs_local_vars' t = raise TERM("program_local_vars\<rightarrow>callproc args",[t])

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
            @{termx "callproc::_\<Rightarrow>(?'aT::procargs,?'bT::prog_type)procedure\<Rightarrow>_\<Rightarrow>_"} $
              Var(("_x",idx),@{typx "?'bT variable"}) $
              proc $
              Var(("_a",idx),@{typx "?'aT procargs"})
        (* val pattern = Drule.instantiate' [] [] callproc_pattern *)
        val callproc = callproc_rule_tac ctx facts
        val obseq = hoare_obseq_replace_tac ctx pattern (SOME callproc) i
     in obseq end)

end
