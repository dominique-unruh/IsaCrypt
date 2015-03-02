(* @SUITE wp *)

theory wp_assign
imports "../Hoare_Tactics"
begin

abbreviation "z == Variable ''z'' :: int variable";

lemma 
  assumes "hoare {P &m} skip {z+2=99}"
  shows "hoare {P &m} z:=z+2 {z=99}"
  apply wp
  by (fact assms)

end
