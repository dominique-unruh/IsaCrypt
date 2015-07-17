theory Tactic_Inline
imports RHL_Typed Hoare_Tactics Procs_Typed
begin

ML_file "tactic_inline.ML"

method_setup inline = {*
  Args.term >> (fn proc => fn ctx => (METHOD (fn facts => Tactic_Inline.inline_tac ctx facts proc 1)))
*} "inlines procedure body"

end