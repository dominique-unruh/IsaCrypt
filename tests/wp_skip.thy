(* @SUITE wp *)

theory wp_skip
imports "../Hoare_Tactics"
begin

abbreviation "z == Variable ''z'' :: int variable";

lemma 
  assumes "hoare {P &m} z<-undefined {z=99}"
  shows "hoare {P &m} z<-undefined; skip {z=99}"
  apply wp
  by (fact assms)

end
