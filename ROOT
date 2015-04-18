session "EasyCrypt" = "HOL-EC-Prereqs" +
  options [document = pdf, quick_and_dirty = true, z3_non_commercial = yes, document_output = "output", browser_info = true]
  theories [document = false]
  theories (*EC_THYS*) ElGamal Ell1 Extended_Sorry Hoare_Tactics Hoare_Typed Hoare_Untyped Lang_Typed Lang_Untyped Modules Procedures RHL_Typed RHL_Untyped Setsum_Infinite TermX_Antiquot Tools Universe
  document_files (in ".")
    "root.tex"


session "HOL-EC-Prereqs" in "~~/src/HOL" = "HOL-Multivariate_Analysis" +
  description {*
    Prerequisites for running the Easycrypt theories.
  *}
  options [document_graph]
  theories
    "Proofs/Lambda/StrongNorm"
    "Proofs/Lambda/Commutation"
    "Probability/Binary_Product_Measure"
