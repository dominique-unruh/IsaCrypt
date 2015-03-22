(* @SUITE modules *)
(* @FAIL *)
(* @ERROR_NOT The error(s) above occurred for the goal statement *)
(* @ERROR_NOT Tactic failed *)

(* TODO: what the output should contain *)

theory moduletype_fail_progtype
imports "../Modules"
begin

typedecl t

moduletype MT where
  f :: "(unit,t) procedure"

moduletype MT' where
  f :: "(t*unit,unit) procedure"

end
