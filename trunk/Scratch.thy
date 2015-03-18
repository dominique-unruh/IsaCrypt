theory Scratch
imports Main Extended_Sorry
begin

lemma bla: "undefined=2 \<and> 2=3" 
  apply rule
  apply (tactic {* cheat_tac_annot (SOME "hello there") @{here} 1 *})
  sorry

ML {*
print_annotated_oracles @{context} @{thm bla};
*}


