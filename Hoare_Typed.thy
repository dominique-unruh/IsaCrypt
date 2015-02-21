theory Hoare_Typed
imports EasyCrypt
begin


definition "(x::int Variable) = mk_variable ''x''"
definition "(y::int Variable) = mk_variable ''y''"
definition "(b::bool Variable) = mk_variable ''b''"

definition "example = mk_seq 
  [mk_assign x (const_expression 0),
   mk_assign b (const_expression True),
   mk_while (var_expression b) (mk_seq [
      mk_sample b (const_expression (uniform UNIV)),
      mk_assign x (apply_expression (const_expression (\<lambda>x. x+1)) x)])]"
lemma well_typed_example: "well_typed example"
  unfolding example_def by simp



lemma assign_rule:
  fixes P Q c x
  assumes "\<forall>m. P m \<longrightarrow> Q (memory_Update m x (E_fun e m))"
  shows "hoare P (mk_assign x e) Q"
  sorry

lemma test: "hoare (\<lambda>m. True) example (\<lambda>m. memory_lookup m b)"
  unfolding example_def
  unfolding mk_seq.simps
  apply (rule seq_rule[where Q="\<lambda>m. memory_lookup m x = 0"])
  apply (rule assign_rule, simp)
  apply (rule seq_rule[where Q="\<lambda>m. memory_lookup m x = 0 \<and> memory_lookup m b = True"])
  apply (rule assign_rule, simp)
  
  sorry
  
end
