theory Extended_Sorry
imports HOL String
keywords
(*  "sorry2" :: "qed" % "proof" *)
  "print_sorry" :: thy_decl
begin

definition "ANNOTATION (prop::prop) (msg::string option) (pos::string) == True"
lemma ANNOTATION: "ANNOTATION prop msg pos" unfolding ANNOTATION_def ..

ML_file "extended_sorry.ML"

lemma test1: assumes "1=1" shows "1=1" sorry
lemma test2: assumes "1=1" shows "1=1" apply (rule test1) sorry
lemma test3: assumes "1=1" shows "1=1" apply (rule test2) sorry
lemma test4: assumes "1=1" shows "1=1" apply (rule test3) sorry

print_sorry test4

(*
lemma bla: "undefined=x" 
  sorry "bla"

print_sorry bla[symmetric]
                      
ML {*
print_annotated_oracles @{context} @{thm bla};
*}
*)

end
