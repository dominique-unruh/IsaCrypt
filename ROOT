session "EasyCrypt" = "HOL-EC-Prereqs" +
  options [document = pdf, quick_and_dirty = true, z3_non_commercial = yes, document_output = "output", browser_info = true]
  theories [document = false]
  theories (*EC_THYS*) ElGamal Ell1 Extended_Sorry Hoare_Tactics Hoare_Typed Hoare_Untyped Lang_Typed Lang_Untyped Modules Procedures RHL_Typed RHL_Untyped Setsum_Infinite TermX_Antiquot Tools Universe
  document_files (in ".")
    "root.tex"


session "HOL-EC-Prereqs" in "~~/src/HOL" = "HOL" +
  description {*
    Lambda Calculus in de Bruijn's Notation.

    This session defines lambda-calculus terms with de Bruijn indixes and
    proves confluence of beta, eta and beta+eta.

    The paper "More Church-Rosser Proofs (in Isabelle/HOL)" describes the whole
    theory (see http://www.in.tum.de/~nipkow/pubs/jar2001.html).
  *}
  options [document_graph]
  theories
    "Proofs/Lambda/StrongNorm"
    "Proofs/Lambda/Commutation"
    "Multivariate_Analysis/Multivariate_Analysis"
    "Probability/Measure_Space"
