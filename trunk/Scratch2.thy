theory Scratch2
imports RHL_Typed Hoare_Tactics
begin

definition "testproc = LOCAL x y a. proc(a) {x:=a; y:=(1::int); return x+y;}"
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

(* If the number of precondition of "inline_rule" changed, need to change the number after NGOALS accordingly.
   inline_rule_conditions_tac is supposed to solve all subgoals of "inline_rule" except the last one. *) 
fun inline_rule_conditions_tac ctx procthms =
  NGOALS 9 (fn i =>
  Raw_Simplifier.rewrite_goal_tac ctx
        [#body_vars procthms, #return_vars procthms, #args procthms] i
    THEN (fast_force_tac ctx i))

fun inline_rule_tac' ctx procthms locals =
  let val inline_rule = @{thm inline_rule} |> Drule.instantiate' [] [NONE, SOME (Thm.cterm_of ctx locals)]
      val simp_rules = @{thms assign_local_vars_typed_simp1[THEN eq_reflection] 
                         assign_local_vars_typed_simp2[THEN eq_reflection] assign_local_vars_typed_simp3[THEN eq_reflection]}
  in rtac inline_rule 1 
     THEN inline_rule_conditions_tac ctx procthms
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#args procthms] 1
     THEN Raw_Simplifier.rewrite_goal_tac ctx simp_rules 1
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#return procthms] 1
     THEN Raw_Simplifier.rewrite_goal_tac ctx [#body procthms] 1
  end

(* TODO: should determine locals ourselves (from procedure_get_body_vars procedure_get_return_vars) *)
fun inline_rule_tac ctx proc locals = 
  let val procthms = procedure_get_thms ctx proc
      val args = Thm.rhs_of (#args procthms)
      val body_vars = Thm.rhs_of (#body_vars procthms)
      val return_vars = Thm.rhs_of (#return_vars procthms)
      val _ = @{print} (args,body_vars,return_vars)
  in
    inline_rule_tac' ctx procthms locals
  end
*}

lemma "LOCAL b c. hoare {b=3} b:=b+2; c:=call testproc(b+1) {c=7}"
  (* TODO: automate this part *)
  apply (rule hoare_obseq_replace[where c="callproc _ _ _" 
      and X="{mk_variable_untyped (LVariable ''b''::int variable), mk_variable_untyped (LVariable ''c''::int variable)}"])
  close (auto intro!: obseq_context_seq obseq_context_assign obseq_context_empty) -- "Show that context allows X-rewriting"
  close (unfold local_assertion_def memory_lookup_def, simp) -- "Show that the postcondition is X-local"

  apply (tactic \<open>inline_rule_tac @{context} @{const testproc}
      @{term "[mk_variable_untyped (LVariable ''x''::int variable), 
               mk_variable_untyped (LVariable ''y''::int variable), 
               mk_variable_untyped (LVariable ''a''::int variable)]"}\<close>)

  apply simp (* TODO: activate simplifier *)

  by (wp, skip, auto)

end
