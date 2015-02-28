theory Example
imports Hoare_Typed RHL_Typed
begin

abbreviation "(x::int variable) == Variable ''x''"
abbreviation "(y::int variable) == Variable ''y''"
abbreviation "(b::bool variable) == Variable ''b''"  

definition "example = 
  PROGRAM[
    x := 0;
    b := True;
    while (b) {
      b <- uniform UNIV;
      x := x+1
    };
    skip;
    if (\<not>b) { skip; x := 15; skip }
  ]"

ML_file "hoare_tactics.ML"

method_setup wp = {* Scan.succeed (K (SIMPLE_METHOD' Hoare_Tactics.wp_tac)) *} "weakest precondition (tail of program: if + assign + skip)"
method_setup wp1 = {* Scan.succeed (K (SIMPLE_METHOD' Hoare_Tactics.wp1_tac)) *} "weakest precondition (last statement only)"
method_setup skip = {* Scan.succeed (K (SIMPLE_METHOD' Hoare_Tactics.skip_tac)) *} "skip"


lemma test: "hoare {Q &m} x := x+1; x := x+1; if (True) x:=4 {x = 15}"
  apply wp
  apply skip
  apply auto
  sorry  

lemma hoare_example: "hoare {True} \<guillemotleft>example\<guillemotright> {x = 15}"
  unfolding example_def program_def
  apply wp apply simp
  apply (rule while_rule'[where I="\<lambda>m. True"], auto)
done

end

