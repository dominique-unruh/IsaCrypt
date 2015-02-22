theory Example
imports Hoare_Typed
begin


abbreviation "(x::int variable) == Variable ''x''"
abbreviation "(y::int variable) == Variable ''y''"
abbreviation "(b::bool variable) == Variable ''b''"  

definition "example = seq 
  [assign x (const_expression 0),
   assign b (const_expression True),
   while (var_expression b) (seq [
      sample b (const_expression (uniform UNIV)),
      assign x (apply_expression (const_expression (\<lambda>x. x+1)) x)])]"
lemma well_typed_example: "well_typed example"
  unfolding example_def by simp
  
lemma test: "hoare (\<lambda>m. True) example (\<lambda>m. \<not> memory_lookup m b)"
  unfolding example_def
  unfolding seq.simps
  apply (rule seq_rule[where Q="\<lambda>m. memory_lookup m x = 0"])
  apply (rule assign_rule, simp)
  apply (rule seq_rule[where Q="\<lambda>m. memory_lookup m x = 0 \<and> memory_lookup m b = True"])
  apply (rule assign_rule, simp)
  apply (rule while_rule[where I="\<lambda>m. True"], auto)
  unfolding hoare_def by auto

