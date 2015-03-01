theory Example
imports Hoare_Typed RHL_Typed
begin

abbreviation "(x::int variable) == Variable ''x''"
abbreviation "(y::int variable) == Variable ''y''"
abbreviation "(b::bool variable) == Variable ''b''"  

definition "example = 
  PROGRAM[
    x := 0;
    b := True;
    while (b) {
      b <- uniform UNIV;
      x := x+1
    };
    skip;
    if (\<not>b) { skip; x := 15; skip }
  ]"

ML_file "hoare_tactics.ML"

method_setup wp = {* Scan.succeed (fn ctx => (SIMPLE_METHOD' (Hoare_Tactics.wp_tac ctx))) *} "weakest precondition (tail of program: if + assign + skip)"
method_setup wp1 = {* Scan.succeed (fn ctx => (SIMPLE_METHOD' (Hoare_Tactics.wp1_tac ctx))) *} "weakest precondition (last statement only)"
method_setup skip = {* Scan.succeed (K (SIMPLE_METHOD' Hoare_Tactics.skip_tac)) *} "skip"


ML "open Hoare_Tactics"

(* TODO: Variables should contain a typeref *)

(*
simproc_setup memory_lookup_update ("memory_lookup (memory_update m v a) w") = {*
let
fun simproc_memory_lookup_update' ctx 
    (Const(@{const_name memory_lookup},_)$
       (Const(@{const_name memory_update},_)$m$v$a) $ w) =
    let val thy = Proof_Context.theory_of ctx
        val vareq = decide_var_eq ctx (cterm_of thy v) (cterm_of thy w) in
    case vareq of NONE => NONE
     | SOME(true,thm) => SOME (@{thm memory_lookup_update_same'} OF [thm])
     | SOME(false,thm) => SOME (@{thm memory_lookup_update_notsame} OF [thm])
    end
  | simproc_memory_lookup_update' _ _ = NONE

fun simproc_memory_lookup_update _ ctx fact =
   simproc_memory_lookup_update' ctx (term_of fact)
in
simproc_memory_lookup_update
end
*}
*)

(*declare [[simproc del: memory_lookup_update]]*)

lemma test: assumes "Q == \<lambda>m. memory_lookup m x = 13"
 (* fixes x::"int variable" and y::"int variable"
  assumes "\<not> var_eq x y"
 *) shows "hoare {\<lambda>m. memory_lookup m x = 13} x := x+1; x := x+1; y := 5; if (False) x:=4 {x \<ge> 15}"
  apply wp
  apply skip
  by simp  

lemma hoare_example: "hoare {True} \<guillemotleft>example\<guillemotright> {x = 15}"
  unfolding example_def program_def
  apply wp apply simp
  apply (rule while_rule'[where I="\<lambda>m. True"], auto)
done

end

