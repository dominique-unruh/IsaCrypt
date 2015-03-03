structure Hoare_Tactics =
struct

fun NGOALS n tac i st =
  tac i st |> Seq.filter (fn st' => nprems_of st' = nprems_of st - 1 + n);
fun NGOALS_ERROR n tac i st =
  tac i st |> Seq.map (fn st' => if nprems_of st' = nprems_of st - 1 + n then st
                                 else raise (ERROR ("NGOALS_ERROR")));

(*
(* Don't forget: fact must have Trueprop in it *)
fun prove_by_tactic ctx tac fact =
  let val thms = Goal.init fact |> (tac THEN ALLGOALS (fn _ => no_tac))
      val thm = (case Seq.pull thms of SOME (thm,_) => thm
                   | NONE => raise (CTERM ("prove_by_tactic: could not prove fact",[fact])))
  in Goal.finish ctx thm end;

fun prove_by_simp ctx fact = 
  prove_by_tactic ctx (simp_tac ctx 1) fact
fun prove_by_asm_simp ctx fact = 
  prove_by_tactic ctx (asm_simp_tac ctx 1) fact

fun is_variable_literal (Const(@{const_name Variable},_)$n) = (HOLogic.dest_string n; true handle TERM _ => false)
  | is_variable_literal (Const(@{const_name LVariable},_)$n) = (HOLogic.dest_string n; true handle TERM _ => false)
  | is_variable_literal _ = false    

fun distinct_types (Type(n1,ts1)) (Type(n2,ts2)) = n1<>n2 orelse distinct_typess ts1 ts2
  | distinct_types _ _ = false
and distinct_typess [] [] = false
  | distinct_typess (t::ts) (u::us) = distinct_types t u orelse distinct_typess ts us
  | distinct_typess _ _ = true (* Different lengths *)

fun decide_var_eq ctx v w =
  let val v' = term_of v
      val w' = term_of w
      val thy = Proof_Context.theory_of ctx
(*      val tv = (case typ_of (ctyp_of_term v) of Type(@{type_name variable},[tv]) => tv | t => raise (TYPE ("decide_var_eq: first arg not type variable",[t],[term_of v])))
      val tw = (case typ_of (ctyp_of_term w) of Type(@{type_name variable},[tw]) => tw | t => raise (TYPE ("decide_var_eq: second arg not type variable",[t],[term_of w])))*)
      fun mk_vareq () = (Const(@{const_name var_eq},fastype_of v' --> fastype_of w' --> HOLogic.boolT)$v'$w')
      fun mk_vareq_not () = cterm_of thy (HOLogic.mk_Trueprop (HOLogic.mk_not (mk_vareq())))
      fun mk_vareq_yes () = cterm_of thy (HOLogic.mk_Trueprop (mk_vareq()))
  in
    (*if distinct_types tv tw then
          SOME (false,@{thm refl}) (*  use typerep to prove inequality *)
    else*) if v' aconv w' then 
         SOME(true,Ctr_Sugar_Util.cterm_instantiate_pos [SOME v] @{thm var_eq_same})
   else if is_variable_literal v' andalso is_variable_literal w' then 
         (* If they were equal literals, they would have been caught by the aconv-check *)
         SOME(false,prove_by_simp ctx (mk_vareq_not()))
    else (* Try to run simplifier to show inequality *)
      (SOME(false,prove_by_asm_simp ctx (mk_vareq_not()))
       handle CTERM _ => (SOME(false,prove_by_asm_simp ctx (mk_vareq_yes()))
                          handle CTERM _ => NONE))
  end
*)

fun simp_memory_updates_tac ctx =
  let val simpset = (Raw_Simplifier.clear_simpset ctx) 
                    addsimps @{thms e_fun_const_expression
                                    e_fun_apply_expression
                                    memory_lookup_update_notsame
                                    memory_lookup_update_same'}
      val simpset = Simplifier.set_subgoaler (fn _ => asm_simp_tac ctx) simpset
  in
    NGOALS 1 (simp_tac simpset)
  end

fun last_step_tac_lax i : tactic = 
  rtac @{thm seq_rule_lastfirst} i
  ORELSE (rtac @{thm addskip_rule} i   THEN   rtac @{thm seq_rule_lastfirst} i)

(* Produces two goals:
  1. A hoare triple with the last statement
  2. A hoare triple with everything before (possibly skip) 

  Fails if the program is only a skip
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

fun wp_if_strict ctx i : tactic =
  rtac @{thm if_case_rule} i
  THEN wp_total_strict_tac ctx i
  THEN wp_total_strict_tac ctx i
  THEN simp_memory_updates_tac ctx i

(* Removes a hoare-triple goal. If the precondition is ?Q, ?Q will be instantiated with the wp *)
and wp_total_strict_tac' ctx i : tactic = (REPEAT_DETERM (wp1_tac ctx i)) THEN (rtac @{thm skip_rule_strict} i)
and wp_total_strict_tac ctx = NGOALS 0 (wp_total_strict_tac' ctx)

and wp1_tac ctx i st =
  (last_step_tac i
  THEN ((rtac @{thm assign_rule_strict} i THEN simp_memory_updates_tac ctx i)
        ORELSE rtac @{thm skip_rule_strict} i
        ORELSE wp_if_strict ctx i))
  st

fun skip_tac i : tactic = Tactic.rtac @{thm skip_rule} i

fun wp_tac ctx i : tactic = REPEAT_DETERM1 (wp1_tac ctx i)

(*fun wp_total_tac i : tactic = (REPEAT_DETERM (wp1_tac i)) THEN (skip_tac i)*)

fun mk_suc_nat n = if n<=0 then @{term "0::nat"} else @{const Suc} $ mk_suc_nat (n-1);

fun program_length (Const(@{const_name seq},_)$p$_) = program_length p + 1
  | program_length _ = 1
fun program_length_hoare (Const(@{const_name hoare},_)$_$p$_) = program_length p
  | program_length_hoare t = raise (TERM ("expreting hoare triple",[t]))

(* TODO: n should count from start *)
(* TODO: I should be allowed to have a more general type (e.g., I=\<lambda>x. True) *)
(* TODO: should be possible to split before first statement *)
fun seq_tac ctx n I =
  SUBGOAL (fn (goal,i) => 
  let val concl = Logic.strip_assums_concl goal
      val proglen = program_length_hoare (HOLogic.dest_Trueprop concl)
      val thy = Proof_Context.theory_of ctx
      val n' = cterm_of thy (mk_suc_nat (proglen - n))
      val insert_split_n = Ctr_Sugar_Util.cterm_instantiate_pos [NONE,SOME n'] @{thm insert_split}
      val seq_rule_Q = (case I of NONE => @{thm seq_rule}
                        | SOME I => Ctr_Sugar_Util.cterm_instantiate_pos [NONE,NONE,SOME (cterm_of thy I)] 
                                    @{thm seq_rule})
  in
  rtac insert_split_n i  
  THEN  Raw_Simplifier.rewrite_goal_tac ctx @{thms split_program_simps} i
  THEN  rtac seq_rule_Q i
  end)



end

