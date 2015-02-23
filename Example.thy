theory Example
imports Hoare_Typed
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

lemma well_typed_example: "well_typed example"
  unfolding example_def program_def by simp

lemma hoare_example: "hoare {\<lambda>m. True} \<guillemotleft>example\<guillemotright> {\<lambda>m. memory_lookup m x = 15}"
  unfolding example_def program_def
  apply (rule seq_rule[where Q="\<lambda>m. \<not> memory_lookup m b"])
  apply (rule seq_rule[where Q="\<lambda>m. memory_lookup m b = True"])
  apply (rule seq_rule[where Q="\<lambda>m. True"])
  apply (rule true_rule, simp)
  apply (rule assign_rule, simp)
  apply (rule while_rule[where I="\<lambda>m. True"], auto)
  apply (rule true_rule, simp)
  apply (rule iftrue_rule, auto)
  apply (rule assign_rule, auto)
done  

