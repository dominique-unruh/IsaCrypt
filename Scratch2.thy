theory Scratch2
imports Procs_Typed
begin

(** REMOVE BELOW **)

consts  p' :: "(unit,unit)procedure \<Rightarrow> (unit,unit)procedure"
lemma x:  "p' q == LOCAL x. proc() { x:=call q(); return () }" sorry

ML "open Conv"

ML {*
val thm = @{thm x}
val lthy = @{context};;

      fun unfold th = top_sweep_conv (K (rewr_conv th)) lthy (* TODO: should fail if no occurrence *)
      val pattern = thm |> Thm.concl_of |> Logic.dest_equals |> fst

      val return = @{termx "p_return (?pattern::(?'a::prog_type, ?'b::prog_type) procedure)"
                      where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold thm then_conv unfold @{thm p_return_simp})

      val body = @{termx "p_body (?pattern::(?'a::prog_type, ?'b::prog_type) procedure)"
                      where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold thm then_conv unfold @{thm p_body_simp})

      val args = @{termx "p_arg (?pattern::(?'a::prog_type, ?'b::prog_type) procedure)"
                      where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold thm then_conv unfold @{thm p_arg_simp})
;;

      val simpset = lthy addsimps @{thms vars_proc_global_locals}
                                                 
      val global_vars = @{termx "set (vars_proc_global (?pattern::(?'a::prog_type, ?'b::prog_type) procedure))"
                          where "?'pattern.1=>(?'a, ?'b) procedure"} |> Thm.cterm_of lthy
            |> (unfold @{thm vars_proc_global_def}
                then_conv unfold args
                then_conv unfold return
                then_conv unfold body
                then_conv Simplifier.rewrite simpset
                then_conv Procs_Typed.procedure_info_conv false lthy
                then_conv Simplifier.rewrite simpset)
*}

(* local_setup {*
  Procs_Typed.register_procedure_thm @{thm x}
*}*)

procedure p' :: "(unit,unit)procedure \<Rightarrow> (unit,unit)procedure" where
  "p' q = LOCAL x. proc() { x:=call q(); return () }"
 
end