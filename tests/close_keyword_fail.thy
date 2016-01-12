(* @SUITE utils *)
(* @FAIL *)
(* @ERROR Method failed to close the subgoal *)

theory close_keyword_fail
imports Main "../Tools"
begin

definition "bla x = x"

lemma "bla x = 1"
  close (auto simp: bla_def)

