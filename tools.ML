structure Tools =
struct

(** Misc tacticals and similar **)

datatype no_return = NoReturn of no_return

fun ASSERT_SUCCESS (tac:tactic) exn st = 
  let val res = tac st 
      val _ = case Seq.pull res of NONE => raise exn | _ => ()
  in res end
fun ASSERT_SUCCESS' (tac:int->tactic) (exn:term->exn) = 
  SUBGOAL (fn (goal,i) => fn st =>
  let val res = tac i st
      val _ = case Seq.pull res of NONE => raise (exn goal) | _ => ()
  in res end)
fun ASSERT_SOLVED' (tac:int->tactic) (exn:term->term list->no_return) = 
  SUBGOAL (fn (goal,i) => fn st =>
  let val res = tac i st
      val solved = Seq.filter (fn st' => Thm.nprems_of st' < Thm.nprems_of st) res
      val _ = case (Seq.pull res, Seq.pull solved) of
                (_,SOME _) => ()
              | (NONE,NONE) => (exn goal []; raise ERROR "impossible")
              | (SOME(st',_),NONE) => (exn goal (Thm.prems_of st'); raise ERROR "impossible")
  in res end)


(** Keyword "close" **)

(* fun method_error kind pos state =
  Seq.single (Proof_Display.method_error kind pos (Proof.raw_goal state)); *)

fun close_with_error_tac ctx int st =
  if Thm.nprems_of st > 0 then
    (if int then (Output.error_message "Method failed to close the subgoal(s)"; 
                  (print_tac ctx "Remaining goal(s) were" THEN ALLGOALS (Skip_Proof.cheat_tac ctx)) st)
            else error "Method failed to close the subgoal(s)")
  else
    all_tac st

fun close_subgoal (text, (_, _)) num int =
  let 
      val _ = writeln ("Interactive: " ^ (if int then "true" else "false"))
      (* val nogoals = (ALLGOALS(K no_tac)) |> SIMPLE_METHOD |> K |> Method.Basic *)              
      val close = Method.Basic (fn ctx => close_with_error_tac ctx int |> SIMPLE_METHOD)
      val text = Method.Combinator (Method.no_combinator_info,Method.Try,[text])
      val text = Method.Combinator (Method.no_combinator_info,Method.Then,[text,close])
      val text = Method.Combinator (Method.no_combinator_info,Method.Select_Goals num,[text])
  in
  (* Seq.APPEND (Proof.apply text #> Seq.make_results, method_error "" pos) *)
  Proof.apply text #> Seq.make_results
  end

val auto_text_range : Method.text_range = (Method.Basic (SIMPLE_METHOD o CHANGED_PROP o auto_tac), (Position.none,Position.none))

val _ =
  Outer_Syntax.command @{command_keyword close} "initial refinement step (unstructured)"
    (Scan.optional Parse.int 1 -- Scan.optional Method.parse auto_text_range >> (fn (num,m) => (Method.report m; Toplevel.proofs' (close_subgoal m num))));

(** Simplifier modulo f **)

(* Call as: hoare_simproc_tac (simplifications@congruences) simpset i : tactic *)
fun fun_equiv_simproc_tac intros ctxt =
  SUBGOAL (fn (goal,i) =>
    case goal of
      Const(@{const_name Trueprop},_) $ (Const(@{const_name fun_equiv},_)$_$_$_) => 
        (resolve0_tac intros THEN_ALL_NEW fun_equiv_simproc_tac intros ctxt) i
        ORELSE (rtac @{thm fun_equiv_refl} i)
    | _ => 
        SOLVED' (simp_tac ctxt) i)

(* A simproc for rewriting goals modulo "fun_equiv f" equivalence (for arbitrary functions f describing the equivalence relation).

   It takes an initializer fact "start" of the form "[| conditions |] ==> goal"
   where each condition is either a normal condition (simplifier will be applied to those),
   or a condition of the form "fun_equiv f A B" (equivalence of A B modulo f).

   Further it takes a list of congruence rules of the form "[| conditions; fun_ext f a_i b_i |] ==> fun_ext f A B"
   where a_i, b_i are supposed to be subterms of A, B (so that applications of that rule descends into A,B),
   and A,B have the same structure except for the subterms a_i,b_i.

   Further it takes simplification rules modulo f of the form "[| conditions |] ==> fun_ext f A B".
   Here B is supposed to be a simplification of A. Simplification rules that hold w.r.t. 
   normal equality (= or ==) do not need to be given, because the are handled by the simplifier directly.

   The congruence rules and the simplification rules are given as a single list, with the simplification rules first.
   That is, intros := (simplification_rules @ congruence_rules).

   "fun_equiv_simproc start intros" is then a simproc ready for being added using simproc_setup.
*)
fun fun_equiv_simproc start intros _ ctxt (t:cterm) = 
  let val fresh_var = Var(("x",Term.maxidx_of_term (Thm.term_of t)+1),Thm.typ_of_cterm t)
      val goal = Logic.mk_equals (Thm.term_of t,fresh_var)
      val thm = Goal.prove ctxt [] [] goal 
                (fn {context,...} => resolve0_tac start 1 THEN ALLGOALS (fun_equiv_simproc_tac intros context))
  in 
    if (Thm.rhs_of thm) aconvc t then NONE else SOME thm
  end
  handle ERROR msg => (warning ("fun_equiv_simproc failed\nTerm was:\n"^(@{make_string} t)^"\nError: "^msg); NONE)

(* Similar to fun_equiv_simproc, except that named theorems are used for the various rules.

   Declare named theorems for start rules, congruence rules, and simplification rules (using the named_theorems command).
   (See fun_equiv_simproc for the meaning of those rule.) Say we used identifiers fstart fcong fsimp.

   Then "fun_equiv_simproc_named @{named_theorems fstart} @{named_theorems fcong} @{named_theorems fsimp}" 
   is a simproc ready for being added with simproc_setup. Theorems can be added later using attributes [fstart],
   [fcong], [fsimp].
*)
fun fun_equiv_simproc_named start cong simp morph ctxt =
  fun_equiv_simproc (Named_Theorems.get ctxt start) (Named_Theorems.get ctxt simp @ Named_Theorems.get ctxt cong) morph ctxt

end
