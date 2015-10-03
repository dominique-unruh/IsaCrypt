(* @SUITE inline *)

theory inline_rename
imports "../Tactic_Inline" "../Lang_Simplifier"
begin

abbreviation "z == Variable ''z'' :: int variable"

procedure proc1 :: "(int,int) procedure" where
  "proc1 = LOCAL x a. proc(a) { x := a; z := x; return z+a }"

(* TODO remove necessity of this *)
local_setup {* Procs_Typed.register_procedure_thm @{thm proc1_def} *}

lemma 
  assumes "LOCAL x a a'. hoare { True } a:=1; a' := z; x := default; x := a'; z := x; z := z+a' { z=undefined }"
  shows "LOCAL a. hoare { True } a:=1; z:=call proc1(z) { z=undefined }"
apply (inline proc1)
apply simp
by (fact assms)

end
