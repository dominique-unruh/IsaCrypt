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

fun wp1_tac i : tactic =
  last_step_tac i
  THEN (rtac @{thm assign_rule_strict} i
        ORELSE rtac @{thm skip_rule_strict} i)

fun wp_tac i : tactic = REPEAT_DETERM1 (wp1_tac i)

fun test_tac ctx =
  SUBGOAL (fn (goal,_) => fn st =>
    (@{print} goal; writeln ("test_tac "^(Syntax.string_of_term ctx goal)); Seq.single st))

end

