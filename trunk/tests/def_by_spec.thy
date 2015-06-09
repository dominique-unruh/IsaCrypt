(* @SUITE procs *)

theory def_by_spec
imports "../Procs_Typed"
begin

lemma four: "2*2=(4::nat)" by auto

definition_by_specification' A::nat where
  "A*A = 4"
  by (rule four)

definition_by_specification p :: "(int*unit,int)procedure" where
  "p = proc(a) { return a; }"

definition_by_specification p :: "(unit,unit)procedure \<Rightarrow> (int*unit,int)procedure" where
  "p q = LOCAL x. proc(a) { x:=callproc q(); return a; }"


(* TODO: test the automatic one once it is independent of procs *)

end
