(* @SUITE seq *)

theory seq
imports "../Hoare_Tactics"
begin

lemma 
  assumes "hoare {P &m} x:=1; x:=2 {x=2}"
  assumes "hoare {x=2} x:=3; x:=4; x:=5; x:=6 {x<10}"
  shows "hoare {P &m} x:=1; x:=2; x:=3; x:=4; x:=5; x:=6 {x<10}"
  apply (seq 2)
  apply (fact assms(1))
  by (fact assms(2))

lemma 
  assumes "hoare {P &m} x:=1; x:=2 {x=2}"
  assumes "hoare {x=2} x:=3; x:=4; x:=5; x:=6 {x<10}"
  shows "hoare {P &m} x:=1; x:=2; x:=3; x:=4; x:=5; x:=6 {x<10}"
  apply (seq 2 invariant: "$x=2")
  apply (fact assms(1))
  by (fact assms(2))

lemma 
  assumes "hoare {P &m} x:=1; x:=2; x:=3; x:=4; x:=5; x:=6 {$x>5}"
  assumes "hoare {$x>5} skip {$x<10}"
  shows "hoare {P &m} x:=1; x:=2; x:=3; x:=4; x:=5; x:=6 {$x<10}"
  apply (seq 6)
  apply (fact assms(1))
  by (fact assms(2))

(* TODO
lemma 
  assumes "hoare {P &m} skip {True}"
  assumes "hoare {True} x:=1; x:=2; x:=3; x:=4; x:=5; x:=6 {$x<10}"
  shows "hoare {P &m} x:=1; x:=2; x:=3; x:=4; x:=5; x:=6 {$x<10}"
  apply (seq 0)
  apply (fact assms(1))
  by (fact assms(2))
*)

end

