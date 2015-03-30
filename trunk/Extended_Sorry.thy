theory Extended_Sorry
imports HOL String
keywords
    "SORRY" :: "qed" % "proof"
and "print_sorry" :: thy_decl
begin

ML " proofs := 0 "

(* TODO: print_sorry should also print:
- val proven_classrels_of = #proven_classrels o rep_data;
val proven_arities_of = #proven_arities o rep_data;
val inst_params_of = #inst_params o rep_data;
But these are not accessible! *)


definition "ANNOTATION (prop::prop) (msg::string option) (pos::string) == True"
lemma ANNOTATION: "ANNOTATION prop msg pos" unfolding ANNOTATION_def ..

ML_file "extended_sorry.ML"

consts testconst :: int
lemma [simp]: "testconst*testconst = 0" SORRY
lemma test1: "testconst*testconst*testconst*testconst = 0"
  by simp
lemma [simp]: "undefined testconst = (0::int)"
proof -
  have x: "undefined testconst == testconst*testconst*testconst*testconst" SORRY
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
