theory Example
imports Hoare_Typed RHL_Typed Hoare_Tactics 
begin 

locale M begin
  abbreviation "(x::int variable) == Variable ''x''"
  definition "invoke == proc (x) { x:=1; return () }"
end

ML {*
  
  fun supertac = ???
*}

method_setup superduper = {* etc *}

lemma "1=2"
  apply (superduper ...)


term M.invoke

abbreviation "(x::int variable) == Variable ''x''"
abbreviation "(y::int variable) == Variable ''y''"
abbreviation "(b::bool variable) == Variable ''b''"  


consts p1::program p2::program p3::program p4::program p5::program p6::program p7::program
definition "test = PROGRAM[ \<guillemotleft>p1\<guillemotright>; \<guillemotleft>p2\<guillemotright>; \<guillemotleft>p3\<guillemotright>; \<guillemotleft>p4\<guillemotright>; \<guillemotleft>p5\<guillemotright>; \<guillemotleft>p6\<guillemotright>; \<guillemotleft>p7\<guillemotright>; ]"

ML {* Scan.lift; Parse.int *}

(* TODO: parse invariant as assertion (with &m, variables, etc) *)
lemma test: "hoare {P &m} x:=1; x:=2; x:=3; x:=4; x:=5; x:=6 {x<10}"
  apply (seq 3 invariant: "x=3")
  apply (wp, skip, simp)
  apply (wp, skip, simp)
done

print_sorry test



definition "example = 
  PROGRAM[
    x := 0;
    b := True;
    while (b) {
      b <- uniform UNIV;
      x := x+1;
    };
    skip;
    if (\<not>b) { skip; x := 15; skip }
  ]"



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

