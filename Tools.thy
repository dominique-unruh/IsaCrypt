theory Tools 
imports Pure
keywords "close" :: "prf_script" % "proof"
begin

ML {*
fun method_error kind pos state =
  Seq.single (Proof_Display.method_error kind pos (Proof.raw_goal state));

fun close_subgoal (text, (pos, _)) =
  let val nogoals = (ALLGOALS(K no_tac)) |> SIMPLE_METHOD |> K |> Method.Basic
      val text = Method.Combinator (Method.no_combinator_info,Method.Then,[text,nogoals])
      val text = Method.Combinator (Method.no_combinator_info,Method.Select_Goals 1,[text])
  in
  Seq.APPEND (Proof.apply text #> Seq.make_results, method_error "" pos)
  end
*}

ML {*
val _ =
  Outer_Syntax.command @{command_keyword close} "initial refinement step (unstructured)"
    (Method.parse >> (fn m => (Method.report m; Toplevel.proofs (close_subgoal m))));
*}

end
