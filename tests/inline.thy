(* @SUITE inline *)

theory inline
imports "../Tactic_Inline" "../Lang_Simplifier"
begin

abbreviation "z == Variable ''z'' :: int variable"

procedure proc1 :: "(int,int) procedure" where
  "proc1 = LOCAL x a. proc(a) { x := a; z := x; return z+a }"

lemma 
  assumes "LOCAL x a. hoare { True } z:=1; a := z; x := default; x := a; z := x; z := z+a { z=undefined }"
  shows "hoare { True } z:=1; z:=call proc1(z) { z=undefined }"
apply (inline proc1)
apply simp
by (fact assms)

end
