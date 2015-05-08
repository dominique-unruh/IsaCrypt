session "EasyCrypt" = "HOL-EC-Prereqs" +
  options [document = pdf, quick_and_dirty = true, (*z3_non_commercial = yes,*) document_output = "output", browser_info = true]
  theories [document = false]
  theories (*EC_THYS*) Distr ElGamal Extended_Sorry Hoare_Tactics Hoare_Typed Hoare_Untyped Lang_Typed Lang_Untyped Modules Procedures Procs_Typed RHL_Typed RHL_Untyped TermX_Antiquot Tools TypedLambda Universe
  document_files (in ".")
    "root.tex"


session "HOL-EC-Prereqs" in "~~/src/HOL" = "HOL-Multivariate_Analysis" +
  description {*
    Prerequisites for running the Easycrypt theories.
  *}
  theories
    "Proofs/Lambda/StrongNorm"
    "Proofs/Lambda/Commutation"
    "Probability/Binary_Product_Measure"

session "HOL-EC-Core" = "HOL-EC-Prereqs" +
  description {*
    Partial IsaCrypt heap
  *}
(*  options [z3_non_commercial = yes] *)
  theories Universe Tools Distr Lang_Untyped TypedLambda

session "HOL-EC-Prereqs-Proofs" = "HOL-EC-Prereqs" +
  theories "~~/src/HOL/Proofs"

session "HOL-EC-Print-Sorry" = "HOL-EC-Prereqs-Proofs" +
  options [(*z3_non_commercial = yes, *) quick_and_dirty = false]
  theories Tmp_Print_Sorry
