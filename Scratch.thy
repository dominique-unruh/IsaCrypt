theory Scratch
imports Procs_Typed Rewrite Hoare_Typed Hoare_Tactics Lang_Simplifier
begin

(** Development of the line-swapping code **)









ML {*

*}

ML {*
*}


ML {*
*}

procedure f where "f = LOCAL x. proc () { x := (1::int); return () }"

procedure g where "g = LOCAL x. proc () { x := call f(); return () }"

lemma
  assumes "LOCAL c3 c4 c5 (x::int variable). hoare {P &m} \<guillemotleft>c1\<guillemotright>; \<guillemotleft>c2\<guillemotright>; c4:=call f(); c5:=x; c3:=x; \<guillemotleft>c6\<guillemotright> {Q &m}"
  shows   "LOCAL c3 c4 c5 (x::int variable). hoare {P &m} \<guillemotleft>c1\<guillemotright>; \<guillemotleft>c2\<guillemotright>; c3:=x; c4:=call f(); c5:=x; \<guillemotleft>c6\<guillemotright> {Q &m}"
apply (rule denotation_eq_rule)
apply (tactic \<open>Hoare_Tactics.swap_tac @{context} ([3],3) 1 1\<close>)
(* close (simp; tactic \<open>CONVERSION (Procs_Typed.procedure_info_conv false @{context}) 1\<close>; simp; tactic \<open>no_tac\<close>) *)
(* close (simp; tactic \<open>CONVERSION (Procs_Typed.procedure_info_conv false @{context}) 1\<close>; simp; tactic \<open>no_tac\<close>) *)
apply simp
by (fact assms)










end
