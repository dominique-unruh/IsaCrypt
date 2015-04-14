(* @SUITE utils *)
(* @FAIL *)
(* @ERROR Failed to apply proof method *)

theory close_keyword_fail2
imports Main "../Tools"
begin

lemma "1=2"
  close auto

