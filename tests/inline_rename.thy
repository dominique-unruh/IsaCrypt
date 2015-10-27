(* @SUITE inline *)

theory inline_rename
imports "../Tactic_Inline" "../Lang_Simplifier"
begin

abbreviation "z == Variable ''z'' :: int variable"

procedure proc1 :: "(int,int) procedure" where
  "proc1 = LOCAL x a. proc(a) { x := a; z := x; return z+a }"

lemma 
  assumes "LOCAL x a aa. hoare { True } a:=(1::int); aa := z; x := default; x := aa; z := x; z := z+aa { z=undefined }"
  shows "LOCAL a. hoare { True } a:=(1::int); z:=call proc1(z) { z=undefined }"
apply (inline proc1)
apply simp
by (fact assms)

end
