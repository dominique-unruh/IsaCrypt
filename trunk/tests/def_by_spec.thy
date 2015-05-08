(* @SUITE wp *)

theory def_by_spec
imports "../Procs_Typed"
begin

lemma four: "2*2=(4::nat)" by auto

definition_by_specification' A::nat where
  "A*A = 4"
  by (rule four)

(* TODO: test the automatic one once it is independent of procs *)

end
