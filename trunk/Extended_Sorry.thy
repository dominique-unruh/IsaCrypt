theory Extended_Sorry
imports HOL String
keywords
    "SORRY" :: "qed" % "proof"
and "print_sorry" :: thy_decl
begin

(* TODO: print_sorry should also print oracles in subclass-proofs *)


definition "ANNOTATION (prop::prop) (msg::string option) (pos::string) == True"
lemma ANNOTATION: "ANNOTATION prop msg pos" unfolding ANNOTATION_def ..

ML_file "extended_sorry.ML"

instantiation nat::finite begin
instance sorry
end
lemma test: "finite (UNIV::nat set)" by (rule finite_UNIV)

print_sorry test

(*
class pro_fun = fixes huhuhisd assumes "huhuhisd \<noteq> huhuhisd"
typedecl ('a,'b) prd
instantiation prd :: (type,type) pro_fun begin
instance SORRY
end

print_sorry classes
*)


end
