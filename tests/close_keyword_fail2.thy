(* @SUITE utils *)
(* @FAIL *)
(* @ERROR Method failed to close the subgoal *)

theory close_keyword_fail2
imports Main "../Tools"
begin

lemma "1=2"
  close auto

