theory Scratch
imports Procs_Typed Rewrite Hoare_Typed Hoare_Tactics Lang_Simplifier
begin

(** Development of the line-swapping code **)









ML {*

fun split_with_seq_tac ctx n =
  if n=0 then resolve_tac ctx @{thms denotation_seq_skip[symmetric]} 
  else if n<0 then error "split_with_seq_tac: n<0"
  else
  SUBGOAL (fn (goal,i) => 
  let
      val concl = Logic.strip_assums_concl goal
      val lhsprog = Hoare_Tactics.dest_denotation (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop concl)))
      val proglen = Hoare_Tactics.program_length lhsprog
      val n' = Thm.cterm_of ctx (Hoare_Tactics.mk_suc_nat (proglen - n))
      val insert_split_n = Drule.infer_instantiate' ctx [SOME n'] @{thm insert_split}
  in
    resolve_tac ctx [insert_split_n] i  
    THEN Raw_Simplifier.rewrite_goal_tac ctx @{thms split_program_simps} i
  end)

*}

ML {*
fun extract_range_tac _   ([],_)   = error "empty range given"
  | extract_range_tac ctx ([a],len) =
      split_with_seq_tac ctx (a-1)
      THEN' resolve_tac ctx @{thms denotation_eq_seq_snd}
      THEN' split_with_seq_tac ctx len
      THEN' resolve_tac ctx @{thms denotation_eq_seq_fst}
  | extract_range_tac _   (_::_::_,_) = error "extract_range_tac: extracting nested ranges not supported"
*}

thm seq_swap

ML {* open Tools *}

ML {*
fun procedure_info_varseteq_tac ctx =
  CONVERSION (Procs_Typed.procedure_info_conv false ctx)
  THEN'
  ASSERT_SOLVED' (simp_tac ctx)
         (fn subgoal1 => fn subgoals => 
            raise TERM("In procedure_info_varseteq_tac, I got subgoal (1).\n"^
                       "I could not prove that subgoal using simp_tac.\n",
                         subgoal1::subgoals))
*}

ML {*
fun swap_tac ctx range len1 i (*(A,B,R)*) =
  extract_range_tac ctx range i
  THEN split_with_seq_tac ctx len1 i
  THEN resolve_tac ctx @{thms seq_swap2} i
  THEN (simp_tac ctx THEN_ALL_NEW procedure_info_varseteq_tac ctx) (i+1)
  THEN (simp_tac ctx THEN_ALL_NEW procedure_info_varseteq_tac ctx) i
*}

procedure f where "f = LOCAL x. proc () { x := (1::int); return () }"

procedure g where "g = LOCAL x. proc () { x := call f(); return () }"

lemma
  assumes "LOCAL c3 c4 c5 (x::int variable). hoare {P &m} \<guillemotleft>c1\<guillemotright>; \<guillemotleft>c2\<guillemotright>; c4:=call f(); c5:=x; c3:=x; \<guillemotleft>c6\<guillemotright> {Q &m}"
  shows   "LOCAL c3 c4 c5 (x::int variable). hoare {P &m} \<guillemotleft>c1\<guillemotright>; \<guillemotleft>c2\<guillemotright>; c3:=x; c4:=call f(); c5:=x; \<guillemotleft>c6\<guillemotright> {Q &m}"
apply (rule denotation_eq_rule)
apply (tactic \<open>swap_tac @{context} ([3],3) 1 1\<close>)
(* close (simp; tactic \<open>CONVERSION (Procs_Typed.procedure_info_conv false @{context}) 1\<close>; simp; tactic \<open>no_tac\<close>) *)
(* close (simp; tactic \<open>CONVERSION (Procs_Typed.procedure_info_conv false @{context}) 1\<close>; simp; tactic \<open>no_tac\<close>) *)
apply simp
by (fact assms)










end
