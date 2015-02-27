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

method_setup wp = {* Scan.succeed (K (SIMPLE_METHOD' Hoare_Tactics.wp_tac)) *} "weakest precondition (incomplete)"
method_setup skip = {* Scan.succeed (K (SIMPLE_METHOD' (Tactic.rtac @{thm skip_rule}))) *} "weakest precondition (incomplete)"
method_setup test = {* Scan.succeed (fn ctx => SIMPLE_METHOD' (Hoare_Tactics.test_tac ctx)) *} "test"

lemma hoare_example: "hoare {True} \<guillemotleft>example\<guillemotright> {x = 15}"
  unfolding example_def program_def
  apply (rule seq_rule, wp)
  apply (rule while_rule'[where I="\<lambda>m. True"], auto)
  apply (rule iftrue_rule, auto)
  apply wp
  apply skip
  apply simp
done

end

