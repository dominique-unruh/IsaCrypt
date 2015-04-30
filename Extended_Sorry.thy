theory Extended_Sorry
imports HOL String
keywords
    "SORRY" :: "qed" % "proof"
and "print_sorry" :: thy_decl
begin

ML " proofs := 0 "

(* TODO: print_sorry should also print oracles in subclass-proofs *)


definition "ANNOTATION (prop::prop) (msg::string option) (pos::string) == True"
lemma ANNOTATION: "ANNOTATION prop msg pos" unfolding ANNOTATION_def ..

ML_file "extended_sorry.ML"

(*
consts bibibi :: "'a\<Rightarrow>bool"
class bla = assumes bibla: "bibibi x"
instantiation unit :: bla begin
instance sorry
end

lemma bi: "bibibi()"
  by (rule bibla)

print_sorry bi*)

end
