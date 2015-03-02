theory Hoare_Tactics
imports Hoare_Typed
begin

ML_file "hoare_tactics.ML"

method_setup wp = {* Scan.succeed (fn ctx => (SIMPLE_METHOD' (Hoare_Tactics.wp_tac ctx))) *} "weakest precondition (tail of program: if + assign + skip)"
method_setup wp1 = {* Scan.succeed (fn ctx => (SIMPLE_METHOD' (Hoare_Tactics.wp1_tac ctx))) *} "weakest precondition (last statement only)"
method_setup skip = {* Scan.succeed (K (SIMPLE_METHOD' Hoare_Tactics.skip_tac)) *} "skip"

(* TODO:

- conseq
- exfalso
- elim*
- seq
- sp
- wp n
- rnd
- if
- while
- call
- proc
- proc*
- swap


*)

end

