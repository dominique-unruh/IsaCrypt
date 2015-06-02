theory Scratch2
imports RHL_Typed Hoare_Tactics
begin

definition "testproc = LOCAL x y a. proc(a) {x:=a; y:=(1::int); return x+y;}"
schematic_lemma testproc_body: "p_body testproc = ?b" unfolding testproc_def by simp
schematic_lemma testproc_return: "p_return testproc = ?b" unfolding testproc_def by simp
schematic_lemma testproc_args: "p_args testproc = ?b" unfolding testproc_def by simp
schematic_lemma testproc_body_vars: "vars (p_body testproc) = ?b" unfolding testproc_body by simp
schematic_lemma testproc_return_vars: "e_vars (p_return testproc) = ?b" unfolding testproc_return by simp



lemma "LOCAL b c. hoare {b=3} b:=b+2; c:=call testproc(b+1) {c=7}"
  apply (rule hoare_obseq_replace[where c="callproc _ _ _" 
      and X="{mk_variable_untyped (LVariable ''b''::int variable), mk_variable_untyped (LVariable ''c''::int variable)}"])
  close (auto intro!: obseq_context_seq obseq_context_assign obseq_context_empty) -- "Show that context allows X-rewriting"
  close (unfold local_assertion_def memory_lookup_def, simp) -- "Show that the postcondition is X-local"

  apply (rule inline_rule[where locals="[mk_variable_untyped (LVariable ''x''::int variable), mk_variable_untyped (LVariable ''y''::int variable), mk_variable_untyped (LVariable ''a''::int variable)]"])
  apply (unfold testproc_body_vars testproc_return_vars testproc_args, auto, tactic "ALLGOALS (K no_tac)")[9] 
     -- "Close all subgoals related to checking the conditions on the variables"

  apply (unfold testproc_args, simp only: procedure.simps assign_local_vars_typed_simp1 assign_local_vars_typed_simp2 assign_local_vars_typed_simp3)

  unfolding testproc_body testproc_return
  by (wp, skip, auto)

end
