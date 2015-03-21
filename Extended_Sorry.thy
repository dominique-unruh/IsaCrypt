theory Extended_Sorry
imports HOL String
keywords
(*  "sorry2" :: "qed" % "proof" *)
  "print_sorry" :: thy_decl
begin

ML " proofs := 0 "


definition "ANNOTATION (prop::prop) (msg::string option) (pos::string) == True"
lemma ANNOTATION: "ANNOTATION prop msg pos" unfolding ANNOTATION_def ..

ML_file "extended_sorry.ML"

consts testconst :: int
lemma [simp]: "testconst*testconst = 0" sorry
lemma test1: "testconst*testconst*testconst*testconst = 0"
  by simp
lemma [simp]: "undefined testconst = (0::int)"
proof -
  have x: "undefined testconst == testconst*testconst*testconst*testconst" sorry
  show ?thesis
    unfolding x by (rule test1)
qed
lemma test2: "undefined testconst + 1 = (1::int)"
  by simp
print_sorry test2

(*
lemma bla: "undefined=x" 
  sorry "bla"

print_sorry bla[symmetric]
                      
ML {*
print_annotated_oracles @{context} @{thm bla};
*}
*)

end
