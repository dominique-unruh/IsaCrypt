theory Scratch2
imports RHL_Typed Hoare_Tactics Lang_Simplifier
begin

abbreviation "g == Variable ''g''"

definition "testproc = LOCAL x y a. proc(a) {x:=a; y:=(1::int); g:=x; return x+y;}"
schematic_lemma testproc_body: "p_body testproc = ?b" unfolding testproc_def by simp
schematic_lemma testproc_return: "p_return testproc = ?b" unfolding testproc_def by simp
schematic_lemma testproc_args: "p_args testproc = ?b" unfolding testproc_def by simp
schematic_lemma testproc_body_vars: "set (vars (p_body testproc)) = ?b" unfolding testproc_body by simp
schematic_lemma testproc_return_vars: "set (e_vars (p_return testproc)) = ?b" unfolding testproc_return by simp


ML {*
fun procedure_get_info suffix ctx proc =
  case proc of 
    Const(procname,_) => Proof_Context.get_thm ctx (procname^suffix) |> Local_Defs.meta_rewrite_rule ctx
  | _ => raise TERM("procedure_get_info expects a constant",[proc])

val procedure_get_args = procedure_get_info "_args";
val procedure_get_body = procedure_get_info "_body";
val procedure_get_return = procedure_get_info "_return";
val procedure_get_body_vars = procedure_get_info "_body_vars";
val procedure_get_return_vars = procedure_get_info "_return_vars";

type procedure_thms = {args:thm, body:thm, return:thm, body_vars:thm, return_vars:thm}

fun procedure_get_thms ctx proc = {
  args=procedure_get_args ctx proc,
  body=procedure_get_body ctx proc,
  return=procedure_get_return ctx proc,
  body_vars=procedure_get_body_vars ctx proc,
  return_vars=procedure_get_return_vars ctx proc
}
*}

ML {*
(* "NGOALS i n tac" applies tac to goals i+n-1,...,n *)
fun NGOALS _ 0 _ st = all_tac st
  | NGOALS i n tac st = (tac (i+n-1) THEN NGOALS i (n-1) tac) st

(* If the number of precondition of "callproc_rule" changed, need to change the number after NGOALS accordingly.
   callproc_rule_conditions_tac is supposed to solve all subgoals of "callproc_rule" except the last one. *) 
fun callproc_rule_conditions_tac ctx procthms i =
  NGOALS i 9 (fn i =>
  Raw_Simplifier.rewrite_goal_tac ctx
        [#body_vars procthms, #return_vars procthms, #args procthms] i
    THEN (fast_force_tac ctx i))

fun callproc_rule_tac' ctx procthms locals i =
  let val callproc_rule = @{thm callproc_rule} |> Drule.instantiate' [] [NONE, SOME (Thm.cterm_of ctx locals)]
      val simp_rules = @{thms assign_local_vars_typed_simp1[THEN eq_reflection] 
                         assign_local_vars_typed_simp2[THEN eq_reflection] assign_local_vars_typed_simp3[THEN eq_reflection]}
  in rtac callproc_rule i
     THEN callproc_rule_conditions_tac ctx procthms i
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#args procthms] i
     THEN Raw_Simplifier.rewrite_goal_tac ctx simp_rules i
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#return procthms] i
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#body procthms] i
  end

fun procedure_local_vars procthms =
  let fun extr1 (Const(@{const_name procargvars_empty},_)) = []
        | extr1 (Const(@{const_name procargvars_add},_) $ v $ rest) = 
            @{termx "mk_variable_untyped (?v::?'w::prog_type variable)" where "?'v.1\<Rightarrow>?'w variable"} :: extr1 rest
        | extr1 t = raise TERM ("callproc_rule_tac: description of arguments contains unexpected subterm",[t])
      fun extr2 (Const(@{const_name Orderings.bot_class.bot},_)) = []
        | extr2 (Const(@{const_name Set.insert},_) $ v $ rest) =
            (case v of Const(@{const_name mk_variable_untyped},_) $ (Const(@{const_name LVariable},_)$_) => v :: extr2 rest
                     | Const(@{const_name mk_variable_untyped},_) $ (Const(@{const_name Variable},_)$_) => extr2 rest (* Drop global vars *)
                     | _ => raise TERM ("callproc_rule_tac: description of body/return contains unexpected subterm",[v]))
        | extr2 t = raise TERM ("callproc_rule_tac: description of body/return contains unexpected subterm",[t])
      val args = Thm.rhs_of (#args procthms) |> Thm.term_of |> extr1
      val body_vars = Thm.rhs_of (#body_vars procthms) |> Thm.term_of |> extr2
      val return_vars = Thm.rhs_of (#return_vars procthms) |> Thm.term_of |> extr2
      val local_vars = args @ body_vars @ return_vars |> distinct (op aconv)
   in local_vars end

(* forbidden := local variables that must not be used *)
(* TODO: should determine the proc itself *)
fun callproc_rule_tac ctx proc forbidden i = 
  let val procthms = procedure_get_thms ctx proc
      val locals = procedure_local_vars procthms
      val _ = if inter (op aconv) locals forbidden = [] then () else
        raise TERM("callproc_rule_tac: locals and forbidden vars have nonempty intersection",
                   [locals |> HOLogic.mk_list @{typ variable_untyped},
                    forbidden |> HOLogic.mk_list @{typ variable_untyped}])
      val locals = HOLogic.mk_list @{typ variable_untyped} locals
  in
    callproc_rule_tac' ctx procthms locals i
  end
*}

ML {*
(* TODO use a more efficient data structure than lists for collecting variables *)
fun program_local_vars' (Const(@{const_name seq},_) $ p1 $ p2) = program_local_vars' p1 @ program_local_vars' p2
  | program_local_vars' (Const(@{const_name program},_) $ p) = program_local_vars' p
  | program_local_vars' (Const(@{const_name assign},_) $ v $ e) = var_if_local' v @ expression_local_vars' e
  | program_local_vars' (Const(@{const_name callproc},_) $ x $ _ $ a) = var_if_local' x @ procargs_local_vars' a
  | program_local_vars' t = raise TERM("program_local_vars",[t])
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
*}

ML {* program_local_vars_untyped @{term "LOCAL b c. PROGRAM[ b:=b+2; c:=call testproc(b+1) ]"} 
  |> HOLogic.mk_set @{typ variable_untyped}
  |> (Thm.cterm_of @{context}) *}

(*ML "procedure_local_vars (procedure_get_thms @{context} @{const testproc}) |> HOLogic.mk_list @{typ variable_untyped} |> (Thm.cterm_of @{context})"*)

ML {*
fun ignore _ x = x

fun hoare_obseq_replace_tac ctx redex obseq_tac =
  SUBGOAL (fn (goal,i) =>
  let 
      val concl = Logic.strip_assums_concl goal
      val program = case concl of @{termx "Trueprop (Hoare_Typed.hoare ?P ?c ?Q)"} => ignore (P,Q) c
                                | t => raise TERM("hoare_obseq_replace_tac: goal not a Hoare triple",[t])
      val program_locals = program_local_vars_untyped program
      val program_locals_set = program_locals |> HOLogic.mk_set @{typ variable_untyped} 
      val obs_eq_vars = @{termx "?program_locals_set \<union> Collect (vu_global::variable_untyped\<Rightarrow>_)"} |> Thm.cterm_of ctx
      val redex = Thm.cterm_of ctx redex
      val callproc_rule = @{thm hoare_obseq_replace} |> Drule.instantiate' [] [SOME obs_eq_vars(*X*),NONE,NONE,SOME redex(*c*)] |> @{print}
  in
    rtac callproc_rule i
    THEN SOLVED' (fast_force_tac (ctx addSIs @{thms obseq_context_seq obseq_context_assign obseq_context_empty})) i
    THEN Raw_Simplifier.rewrite_goal_tac ctx @{thms assertion_footprint_def memory_lookup_def} i
    THEN SOLVED' (fast_force_tac ctx) i
    THEN obseq_tac program_locals i
  end)
*}

lemma "\<And>z. LOCAL b c x. hoare {b=3} b:=$b+2; c:=call testproc(b+z) {c=6+z}"
apply (tactic {*
let val callproc = callproc_rule_tac @{context} @{const testproc}
    val obseq = hoare_obseq_replace_tac @{context} (Proof_Context.read_term_pattern @{context} "callproc _ _ _") callproc 1
in
obseq
end
*})

(*
apply (tactic \<open>hoare_obseq_replace_tac @{context} (Proof_Context.read_term_pattern @{context} "callproc _ _ _") (K (K all_tac)) 1\<close>)
(*apply (rule hoare_obseq_replace[where c="callproc _ _ _" and 
  X="{mk_variable_untyped (LVariable ''b''::int variable), mk_variable_untyped (LVariable ''c''::int variable)} \<union> Collect vu_global"])
  close (auto intro!: obseq_context_seq obseq_context_assign obseq_context_empty) -- "Show that context allows X-rewriting"
  close (unfold assertion_footprint_def memory_lookup_def, fastforce) -- "Show that the postcondition is X-local"  *)

  apply (tactic "callproc_rule_tac @{context} @{const testproc} [] 1")
(*  apply (rule callproc_rule[where locals = "[mk_variable_untyped (LVariable ''x''::int variable), mk_variable_untyped (LVariable ''y''::int variable), mk_variable_untyped (LVariable ''a''::int variable)]"])
  apply (unfold testproc_body_vars testproc_args testproc_return_vars, auto)[9] *)
*)
  by (wp, skip, simp)

end
