(* @SUITE procs *)

theory def_by_spec
imports "../Procs_Typed"
begin

lemma four: "2*2=(4::nat)" by auto

definition_by_specification' A::nat where
  "A*A = 4"
  by (rule four)

(* Test whether leftover schematic variables are a problem *)
lemma extra_y: "x == fst (x,y)" by auto
definition_by_specification' B::nat where
  "B = 4"
  apply (subst extra_y[of 4]) 
  by (fact refl)

definition_by_specification p :: "(int*unit,int)procedure" where
  "p = LOCAL a. proc(a) { skip; return a }"

definition_by_specification p' :: "(unit,unit)procedure \<Rightarrow> (int*unit,int)procedure" where
  "p' q = LOCAL a x. proc(a) { x:=call q(); return a }"

end
