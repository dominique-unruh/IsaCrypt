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
fun NGOALS 0 _ st = all_tac st
  | NGOALS n tac st = (tac n THEN NGOALS (n-1) tac) st

(* If the number of precondition of "callproc_rule" changed, need to change the number after NGOALS accordingly.
   callproc_rule_conditions_tac is supposed to solve all subgoals of "callproc_rule" except the last one. *) 
fun callproc_rule_conditions_tac ctx procthms =
  NGOALS 9 (fn i =>
  Raw_Simplifier.rewrite_goal_tac ctx
        [#body_vars procthms, #return_vars procthms, #args procthms] i
    THEN (fast_force_tac ctx i))

fun callproc_rule_tac' ctx procthms locals =
  let val callproc_rule = @{thm callproc_rule} |> Drule.instantiate' [] [NONE, SOME (Thm.cterm_of ctx locals)]
      val simp_rules = @{thms assign_local_vars_typed_simp1[THEN eq_reflection] 
                         assign_local_vars_typed_simp2[THEN eq_reflection] assign_local_vars_typed_simp3[THEN eq_reflection]}
  in rtac callproc_rule 1 
     THEN callproc_rule_conditions_tac ctx procthms
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#args procthms] 1
     THEN Raw_Simplifier.rewrite_goal_tac ctx simp_rules 1
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#return procthms] 1
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#body procthms] 1
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

fun callproc_rule_tac ctx proc = 
  let val procthms = procedure_get_thms ctx proc
      val locals = HOLogic.mk_list @{typ variable_untyped} (procedure_local_vars procthms)
  in
    callproc_rule_tac' ctx procthms locals
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

lemma "LOCAL b c. hoare {b=3} b:=b+2; c:=call testproc(b+1) {c=7}"
  (* TODO: automate this part *)
(*  apply (rule hoare_obseq_replace[where c="callproc _ _ _" 
      and X="{mk_variable_untyped (LVariable ''b''::int variable), mk_variable_untyped (LVariable ''c''::int variable)} \<union> {x. vu_global x}"])
  close (auto intro!: obseq_context_seq obseq_context_assign obseq_context_empty) -- "Show that context allows X-rewriting"
  close (unfold assertion_footprint_def memory_lookup_def, fastforce) -- "Show that the postcondition is X-local" *)

apply (rule hoare_obseq_replace[where c="callproc _ _ _" and 
(* This one is program_local_vars_untyped + Collect vu_global *)
X="{mk_variable_untyped (LVariable ''b''::int variable), mk_variable_untyped (LVariable ''c''::int variable)} \<union> Collect vu_global"])
  close (auto intro!: obseq_context_seq obseq_context_assign obseq_context_empty) -- "Show that context allows X-rewriting"
  close (unfold assertion_footprint_def memory_lookup_def, fastforce) -- "Show that the postcondition is X-local" 

(*  apply (rule callproc_rule[where locals = "[mk_variable_untyped (LVariable ''x''::int variable), mk_variable_untyped (LVariable ''y''::int variable), mk_variable_untyped (LVariable ''a''::int variable)]"])
  apply (unfold testproc_body_vars testproc_args testproc_return_vars, auto)[9] *)
  apply (tactic "callproc_rule_tac @{context} @{const testproc}")

  apply simp

  by (wp, skip, simp)

end
