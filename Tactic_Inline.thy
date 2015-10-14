theory Tactic_Inline
imports RHL_Typed Hoare_Tactics Procs_Typed
begin

(*definition "HIDDEN_EQ = op="
lemma HIDDEN_EQ_refl: "HIDDEN_EQ x x" unfolding HIDDEN_EQ_def ..
lemma HIDDEN_EQ_I': "HIDDEN_EQ a b \<Longrightarrow> a==b" by (simp add: HIDDEN_EQ_def)
lemma HIDDEN_EQ_ok:
  shows "HIDDEN_EQ procargvars_empty procargvars_empty" 
  and   "HIDDEN_EQ v w \<Longrightarrow> HIDDEN_EQ (procargvars_add (LVariable n) v) (procargvars_add (LVariable n) w)"
  and   "HIDDEN_EQ v w \<Longrightarrow> HIDDEN_EQ (procargvars_add (Variable n) v) (procargvars_add (Variable n) w)"
unfolding HIDDEN_EQ_def by simp_all *)
 
lemma obs_eq'_rename_variables_proc:
  assumes "obs_eq' V (callproc x (rename_local_variables_proc ren prc) args) body"
  shows "obs_eq' V (callproc x prc args) body"
using assms unfolding obs_eq'_def obs_eq_def rhoare_def denotation_callproc_rename_local_variables_proc .

thm obs_eq'_rename_variables_proc[of _ _ "[]"]

ML_file "tactic_inline.ML"
                                                                    
method_setup inline = {*
  Args.term >> (fn proc => fn ctx => (METHOD (fn facts => Tactic_Inline.inline_tac ctx facts proc 1)))
*} "inlines procedure body"

end