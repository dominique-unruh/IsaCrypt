theory wp_if
imports "../Hoare_Tactics"
begin

abbreviation "z == Variable ''z'' :: int variable";
abbreviation "a == Variable ''a'' :: int variable";

lemma 
  assumes "hoare {P &m} skip {if a=0 then z+1=99 else z+2=99}"
  shows "hoare {P &m} if (a=0) z:=z+1 else z:=z+2 {z=99}"
  apply wp
  by (fact assms)

end
