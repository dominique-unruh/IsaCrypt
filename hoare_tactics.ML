structure Hoare_Tactics =
struct

fun last_step_tac_lax i : tactic = 
  rtac @{thm seq_rule_lastfirst} i
  ORELSE (rtac @{thm addskip_rule} i   THEN   rtac @{thm seq_rule_lastfirst} i)

(* Produces two goals:
  1. A hoare triple with the last statement
  2. A hoare triple with everything before (possibly skip) 
*)
val last_step_tac : int -> tactic =
  SUBGOAL (fn (goal,i) => 
    let val concl = Logic.strip_assums_concl goal
    in 
    case concl of
      Const(@{const_name Trueprop},_) $ 
        (Const(@{const_name hoare},_) $ _ $ Const(@{const_name skip},_) $ _) => no_tac
    | _ => last_step_tac_lax i
    end)

fun wp_if_strict i : tactic =
  rtac @{thm if_case_rule} i
  THEN wp_total_strict_tac i
  THEN wp_total_strict_tac i

(* Removes a hoare-triple goal. If the precondition is ?Q, ?Q will be instantiated with the wp *)
and wp_total_strict_tac i : tactic = (REPEAT_DETERM (wp1_tac i)) THEN (rtac @{thm skip_rule_strict} i)

and wp1_tac i st =
  (last_step_tac i
  THEN (rtac @{thm assign_rule_strict} i
        ORELSE rtac @{thm skip_rule_strict} i
        ORELSE wp_if_strict i))
  st

fun skip_tac i : tactic = Tactic.rtac @{thm skip_rule} i

fun wp_tac i : tactic = REPEAT_DETERM1 (wp1_tac i)

fun wp_total_tac i : tactic = (REPEAT_DETERM (wp1_tac i)) THEN (skip_tac i)


end

