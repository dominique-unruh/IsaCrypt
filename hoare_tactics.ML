structure Hoare_Tactics =
struct

datatype side = SideHoare | SideLeft | SideRight | SideBoth

fun NGOALS n tac i st =
  tac i st |> Seq.filter (fn st' => Thm.nprems_of st' = Thm.nprems_of st - 1 + n);
(* fun NGOALS_ERROR n tac i st =
  tac i st |> Seq.map (fn st' => if Thm.nprems_of st' = Thm.nprems_of st - 1 + n then st
                                 else raise (ERROR ("NGOALS_ERROR"))); *)


(* TODO: 
  - add lookup_update for patterns
  - update_pattern (variable_pattern)
  - update_pattern (pair_pattern)
*)

fun simp_memory_updates_tac ctx =
  let val simpset = (Raw_Simplifier.clear_simpset ctx) 
                    addsimps @{thms e_fun_const_expression
                                    e_fun_apply_expression
                                    memory_update_variable_pattern
                                    memory_update_pair_pattern
                                    memory_update_unit_pattern
                                    memory_lookup_update_notsame
                                    memory_lookup_update_same'}
      val simpset = Simplifier.set_subgoaler (fn _ => asm_simp_tac ctx) simpset
  in
    NGOALS 1 (simp_tac simpset)
  end

fun last_step_tac_lax side i : tactic = 
  let val (assoc,lastfirst,addskip) =
      case side of SideHoare => (@{thm seq_assoc_rule},@{thm seq_rule_lastfirst},@{thm addskip_rule})
                 | SideLeft => (@{thm seq_assoc_left_rule},@{thm seq_rule_lastfirst_left},@{thm addskip_left_rule})
                 | SideRight => (@{thm seq_assoc_right_rule},@{thm seq_rule_lastfirst_right},@{thm addskip_right_rule})
                 | SideBoth => error "last_step_tac_lax: SideBoth not supported"
  in    
  (REPEAT (resolve0_tac [assoc] i)   THEN   resolve0_tac [lastfirst] i)
  ORELSE (resolve0_tac [addskip] i   THEN   resolve0_tac [lastfirst] i)
  end

(* 
  Expects goal: hoare {...} ... {...}

  Produces two goals:
  1. A hoare triple with the last statement
  2. A hoare triple with everything before (possibly skip) 
  (If the goal is of the form a;(b;c), it will make it into "c" and "a;b")

  Fails if the program is only a skip
*)
fun last_step_tac side : int -> tactic =
  SUBGOAL (fn (goal,i) => 
    let val concl = Logic.strip_assums_concl goal
    in 
    case (side,concl) of
      (SideHoare, Const(@{const_name Trueprop},_) $ 
        (Const(@{const_name hoare},_) $ _ $ Const(@{const_name skip},_) $ _)) => no_tac
    | (SideLeft, Const(@{const_name Trueprop},_) $ 
        (Const(@{const_name rhoare},_) $ _ $ Const(@{const_name skip},_) $ _ $ _)) => no_tac
    | (SideRight, Const(@{const_name Trueprop},_) $ 
        (Const(@{const_name rhoare},_) $ _ $ _ $ Const(@{const_name skip},_) $ _)) => no_tac
    | _ => last_step_tac_lax side i
    end)

type wp_config = {
  nondeterministic_sample : bool, (* Should wp/wp1 also remove "x <- e" statements (treated as nondeterministic assignments) *)
  side : side (* where to apply wp *)
}
val wp_config_default = {nondeterministic_sample=false, side=SideBoth}
fun wp_config_update_nondeterministic_sample {side,...} b : wp_config = {nondeterministic_sample=b,side=side}
fun wp_config_update_side ({nondeterministic_sample,...}:wp_config) b : wp_config = {nondeterministic_sample=nondeterministic_sample,side=b}

fun update_parser (parser:'a context_parser) (update:'b->'a->'b) (state:'b) : ('b context_parser) =
(*  prev :|-- (fn state =>*)
    (parser >> update state) || Scan.succeed state

(* local
fun parse conf toks = 
  
  ((Scan.lift (Parse.reserved "sample") |-- parse (wp_config_update_nondeterministic_sample conf true)) ||
  Scan.succeed conf) toks
in *)
val wp_config_parser : wp_config context_parser = 
  Scan.lift (Scan.succeed wp_config_default)
  :|--
  update_parser (Scan.lift (Parse.reserved "sample")) (fn conf => fn _ => wp_config_update_nondeterministic_sample conf true)
  :|--
  update_parser (Scan.lift (Parse.reserved "left")) (fn conf => fn _ => wp_config_update_side conf SideLeft) 
  :|--
  update_parser (Scan.lift (Parse.reserved "right")) (fn conf => fn _ => wp_config_update_side conf SideRight) 

fun assert_tac b tac = if b then tac else no_tac

(* Solves a goal of the form "hoare {?P} if e then p1 else p2 {...}" 
   by instantiating ?P with the weakest precondition. *)
fun wp_if_strict ctx (conf:wp_config) : int -> tactic =
  let val if_case = case #side conf of SideHoare => @{thm if_case_rule}
                                     | SideLeft => @{thm if_case_rule_left}
                                     | SideRight => @{thm if_case_rule_right}
                                     | SideBoth => error "wp_if_strict: SideBoth not supported"
  in
    resolve_tac ctx [if_case]
    THEN' wp_total_strict_tac conf ctx
    THEN' wp_total_strict_tac conf ctx
    THEN' simp_memory_updates_tac ctx
  end

(* Removes a hoare-triple goal. If the precondition is ?Q, ?Q will be instantiated with the wp *)
and wp_total_strict_tac' ctx conf i : tactic = 
  let val skip_rule = case #side conf of SideHoare => @{thm skip_rule_strict}
                                       | SideLeft => @{thm rskip_rule_strict}
                                       | SideRight => @{thm rskip_rule_strict}
                                       | SideBoth => error "wp_total_strict_tac': SideBoth not supported"
  in
    REPEAT_DETERM (wp1_tac' ctx conf i) THEN (resolve_tac ctx [skip_rule] i)
  end
and wp_total_strict_tac ctx conf = NGOALS 0 (wp_total_strict_tac' conf ctx)

and wp1_tac' ctx conf i st =
  let val (assign,sample,skip) = case #side conf of SideHoare => (@{thm assign_rule_strict},@{thm sample_rule_strict},@{thm skip_rule_strict})
                                                  | SideLeft => (@{thm assign_rule_left_strict},@{thm refl}(*not used*),@{thm rskip_rule_strict})
                                                  | SideRight => (@{thm assign_rule_right_strict},@{thm refl}(*not used*),@{thm rskip_rule_strict})
                                                  | SideBoth => error "wp1_tac': SideBoth not supported"
  in
    (last_step_tac (#side conf) i
    THEN ((resolve_tac ctx [assign] i THEN simp_memory_updates_tac ctx i)
          ORELSE assert_tac (#nondeterministic_sample conf) (case #side conf of SideHoare => resolve_tac ctx [sample] i THEN simp_memory_updates_tac ctx i
                                                                              | _ => fn _ => error "wp1_tac: nondeterministic_sample not supported for RHL")
          ORELSE resolve_tac ctx [skip] i
          ORELSE wp_if_strict ctx conf i))
    st
  end

val skip_tac = resolve0_tac @{thms skip_rule rskip_rule}

datatype hoare_kind = HoareRHL | HoarePossibilistic | HoareInvalid

fun hoare_kind (Const(@{const_name Trueprop},_) $ (Const(@{const_name Hoare_Typed.hoare},_) $ _ $ _ $ _)) = HoarePossibilistic
  | hoare_kind (Const(@{const_name Trueprop},_) $ (Const(@{const_name rhoare},_) $ _ $ _ $ _ $ _)) = HoareRHL
  | hoare_kind _ = HoareInvalid

fun wp_tac ctx conf : int -> tactic = 
  case #side conf of
    SideBoth => SUBGOAL (fn (goal,i) => case hoare_kind goal of
      HoarePossibilistic => wp_tac ctx (wp_config_update_side conf SideHoare) i
    | HoareRHL => CHANGED ((TRY (wp_tac ctx (wp_config_update_side conf SideLeft) i))
                      THEN (TRY (wp_tac ctx (wp_config_update_side conf SideRight) i)))
    | HoareInvalid => error "wp_tac: HoareInvalid")
  | _ => fn i => REPEAT_DETERM1 (wp1_tac' ctx conf i)

fun wp1_tac ctx conf : int -> tactic =
  case #side conf of
    SideBoth => SUBGOAL (fn (goal,i) => case hoare_kind goal of
      HoarePossibilistic => wp1_tac' ctx (wp_config_update_side conf SideHoare) i
    | HoareRHL => wp1_tac' ctx (wp_config_update_side conf SideLeft) i
                  ORELSE wp1_tac' ctx (wp_config_update_side conf SideRight) i
    | HoareInvalid => error "wp1_tac: HoareInvalid")
  | _ => wp1_tac' ctx conf

fun mk_suc_nat n = if n<=0 then @{term "0::nat"} else @{const Suc} $ mk_suc_nat (n-1);

fun program_length (Const(@{const_name seq},_)$p$_) = program_length p + 1
  | program_length _ = 1
(*fun program_length_hoare (Const(@{const_name hoare},_)$_$p$_) = program_length p
  | program_length_hoare t = raise (TERM ("expecting hoare triple",[t]))*)

fun dest_denotation (Const (@{const_name denotation}, _) $ p) = p
  | dest_denotation t = raise TERM ("dest_denotation", [t])


(*
  Proves the goal "denotation c = denotation ?d" by
  instantiating ?d with (seq c1 c2) where c1 are the first n statements of c
*)
fun seq_deno_tac ctx n =
  if n=0 then resolve_tac ctx @{thms denotation_seq_skip[symmetric]} 
  else
  SUBGOAL (fn (goal,i) => 
  let
      val concl = Logic.strip_assums_concl goal
      val lhsprog = dest_denotation (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop concl)))
      val proglen = program_length lhsprog
      val n' = Thm.cterm_of ctx (mk_suc_nat (proglen - n))
      val insert_split_n = Drule.infer_instantiate' ctx [SOME n'] @{thm insert_split}
  in
    resolve_tac ctx [insert_split_n] i  
    THEN Raw_Simplifier.rewrite_goal_tac ctx @{thms split_program_simps} i
    THEN resolve_tac ctx @{thms HOL.refl} i
  end)

fun seq_tac ctx n I i =
  let
      val seq_rule_Q = (case I of NONE => @{thm seq_rule}
                        | SOME I => Drule.infer_instantiate' ctx [NONE,NONE,SOME (Thm.cterm_of ctx I)] 
                                    @{thm seq_rule})
  in
  resolve_tac ctx @{thms denotation_eq_rule} i
  THEN  seq_deno_tac ctx n i
  THEN  resolve_tac ctx [seq_rule_Q] i
  end

(* In a goal "denotation xxx = denotation ?c", splits xxx at position n, leaving two such goals *)
fun split_with_seq_tac ctx n =
  if n=0 then resolve_tac ctx @{thms denotation_seq_skip[symmetric]} 
  else if n<0 then error "split_with_seq_tac: n<0"
  else
  SUBGOAL (fn (goal,i) => 
  let
      val concl = Logic.strip_assums_concl goal
      val lhsprog = dest_denotation (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop concl)))
      val proglen = program_length lhsprog
      val n' = Thm.cterm_of ctx (mk_suc_nat (proglen - n))
      val insert_split_n = Drule.infer_instantiate' ctx [SOME n'] @{thm insert_split}
  in
    resolve_tac ctx [insert_split_n] i  
    THEN Raw_Simplifier.rewrite_goal_tac ctx @{thms split_program_simps} i
  end)

(* Takes a range in a program (i.e., a path, and a length), and extracts that range in xxx a goal
  of the form "denotation xxx = denotation ?x"

  (only partially implemented)
*)
fun extract_range_tac _   ([],_)   = error "empty range given"
  | extract_range_tac ctx ([a],len) =
      split_with_seq_tac ctx (a-1)
      THEN' resolve_tac ctx @{thms denotation_eq_seq_snd}
      THEN' split_with_seq_tac ctx len
      THEN' resolve_tac ctx @{thms denotation_eq_seq_fst}
  | extract_range_tac _   (_::_::_,_) = error "extract_range_tac: extracting nested ranges not supported"

(* Swaps two code parts in a goal of the form "denotation xxx = denotation ?c"

  The parts are specified by giving a range (that contains both parts), and an index len1
  giving the length of the first *)
fun swap_tac ctx range len1 i =
  extract_range_tac ctx range i
  THEN split_with_seq_tac ctx len1 i
  THEN resolve_tac ctx @{thms seq_swap2} i
  THEN (simp_tac ctx THEN_ALL_NEW Procs_Typed.procedure_info_varseteq_tac ctx) (i+1)
  THEN (simp_tac ctx THEN_ALL_NEW Procs_Typed.procedure_info_varseteq_tac ctx) i


end

