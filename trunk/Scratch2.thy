theory Scratch2
imports RHL_Typed Hoare_Tactics
begin

(* TODO move *)
lemma memory_lookup_untyped_mk_variable_untyped [simp]:
  "memory_lookup_untyped m (mk_variable_untyped x) = embedding (memory_lookup m x)"
SORRY

declare embedding_inv'[simp]

experiment begin

definition "testproc = LOCAL x y a. proc(a) {x:=a; y:=(1::int); return x+y;}"
lemma "LOCAL b c. hoare {b=3} b:=b+2; c:=call testproc(b+1) {c=7}"
  apply (rule hoare_obseq_replace[where c="callproc _ _ _" 
      and X="mk_variable_untyped ` {LVariable ''b''::int variable, LVariable ''c''::int variable}"])
  close (auto intro!: obseq_context_seq obseq_context_assign obseq_context_empty)
  apply (unfold testproc_def, rule inline_rule[where locals="[mk_variable_untyped (LVariable ''x''::int variable), mk_variable_untyped (LVariable ''y''::int variable), mk_variable_untyped (LVariable ''a''::int variable)]"]; simp)
  close auto
  close auto
  close auto
  close auto
  unfolding local_assertion_def memory_lookup_def close auto
  unfolding program_def testproc_def apply simp
  
  apply (rule seq_rule_lastfirst)
  apply wp
  apply (rule seq_rule_lastfirst)
  apply wp
  apply (skip; auto; fail)
  apply wp
  apply (skip; auto; fail)
  apply wp
  apply (skip) apply auto
done

end
