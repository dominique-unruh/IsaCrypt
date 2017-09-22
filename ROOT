session "IsaCrypt" = "HOL-Probability" + 
  options [document = pdf, quick_and_dirty = true, (*z3_non_commercial = yes,*) document_output = "output", browser_info = true]
  sessions "HOL-Nominal" "HOL-Proofs-Lambda" "HOL-ZF"
  theories [document = false]
  theories (*ISACRYPT_THYS*) Distr ElGamal Hoare_Tactics Hoare_Typed Hoare_Untyped Lang_Simplifier Lang_Typed Lang_Untyped Misc Procedures Procs_Typed RHL_Typed RHL_Untyped Tactic_Inline TermX_Antiquot Tools TypedLambda TypedLambdaNominal Universe
  document_files (in ".")
    "root.tex"

session "IsaCrypt-Partial" = "IsaCrypt-Prereqs" +
  theories Universe TypedLambda

session "IsaCrypt-Prereqs" = "HOL-Probability" +
  sessions "HOL-Nominal" "HOL-Proofs-Lambda" "HOL-ZF"
  theories [document = false] Prereqs

(*
session "IsaCrypt-Prereqs" in "~~/src/HOL" = "HOL-Analysis" +
  description {*
    Prerequisites for running the IsaCrypt theories.
  *}
  theories
(*    "Proofs/Lambda/StrongNorm"
    "Proofs/Lambda/Commutation"
    "Probability/Binary_Product_Measure"
    "Eisbach/Eisbach" *)
    "Proofs/Lambda/Commutation"
    "Proofs/Lambda/ListOrder"
    "Library/Rewrite"
    "Nominal/Nominal"
*)
