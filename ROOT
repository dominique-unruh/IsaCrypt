session "IsaCrypt" = "IsaCrypt-Prereqs" +
  options [document = pdf, quick_and_dirty = true, (*z3_non_commercial = yes,*) document_output = "output", browser_info = true]
  theories [document = false]
  theories (*ISACRYPT_THYS*) Distr ElGamal Hoare_Tactics Hoare_Typed Hoare_Untyped Lang_Simplifier Lang_Typed Lang_Untyped Misc Procedures Procs_Typed RHL_Typed RHL_Untyped Tactic_Inline TermX_Antiquot Tools TypedLambda TypedLambdaNominal Universe
  document_files (in ".")
    "root.tex"

session "IsaCrypt-Nodocs" = "IsaCrypt-Prereqs" +
  options [document = false, quick_and_dirty = true]
  theories [document = false]
  theories (*ISACRYPT_THYS*) Distr ElGamal Hoare_Tactics Hoare_Typed Hoare_Untyped Lang_Simplifier Lang_Typed Lang_Untyped Misc Procedures Procs_Typed RHL_Typed RHL_Untyped Tactic_Inline TermX_Antiquot Tools TypedLambda TypedLambdaNominal Universe
  document_files (in ".")
    "root.tex"


session "IsaCrypt-Prereqs" in "~~/src/HOL" = "HOL-Analysis" +
  description {*
    Prerequisites for running the IsaCrypt theories.
  *}
  theories
(*    "Proofs/Lambda/StrongNorm"
    "Proofs/Lambda/Commutation"
    "Probability/Binary_Product_Measure"
    "Library/Rewrite"
    "Eisbach/Eisbach" *)
    "Nominal/Nominal"

session "IsaCrypt-Core" = "IsaCrypt-Prereqs" +
  description {*
    Partial IsaCrypt heap
  *}
  theories Universe Tools Distr Lang_Untyped TypedLambda TermX_Antiquot

session "IsaCrypt-Prereqs-Proofs" = "IsaCrypt-Prereqs" +
  theories "~~/src/HOL/Proofs"

session "IsaCrypt-Print-Sorry" = "IsaCrypt-Prereqs-Proofs" +
  options [(*z3_non_commercial = yes, *) quick_and_dirty = false]
  theories Tmp_Print_Sorry
