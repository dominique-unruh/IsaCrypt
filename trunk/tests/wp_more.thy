(* @SUITE wp *)

theory wp_more
imports "../Hoare_Tactics"
begin

lemma 
  assumes "hoare {$z=0} skip {$z+1+2+3+4+5=15}"
  shows "hoare {$z=0} z:=z+1; (z:=z+2; z:=z+3; z:=z+4); z:=z+5 {$z=15}"
  apply wp
  by (fact assms)

end
