theory Extended_Sorry
imports HOL String
keywords
    "SORRY" :: "qed" % "proof"
and "print_sorry" :: thy_decl
begin

ML " proofs := 1 "

(* TODO: print_sorry should also print oracles in subclass-proofs *)


definition "ANNOTATION (prop::prop) (msg::string option) (pos::string) == True"
lemma ANNOTATION: "ANNOTATION prop msg pos" unfolding ANNOTATION_def ..

ML_file "extended_sorry.ML"

end
