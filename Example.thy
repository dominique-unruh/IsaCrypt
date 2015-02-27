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
    if (\<not>b) x := 15
  ]"

lemma hoare_example: "hoare {True} \<guillemotleft>example\<guillemotright> {x = 15}"
  unfolding example_def program_def
  apply (rule seq_rule[where Q="\<lambda>m. \<not> memory_lookup m b"])
  apply (rule while_rule'[where I="\<lambda>m. True"], auto)
  apply (rule iftrue_rule, auto)
  apply (rule assign_rule, auto)
done

