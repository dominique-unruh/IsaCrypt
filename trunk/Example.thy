theory Example
imports Hoare_Typed RHL_Typed Hoare_Tactics
begin

abbreviation "(x::int variable) == Variable ''x''"
abbreviation "(y::int variable) == Variable ''y''"
abbreviation "(b::bool variable) == Variable ''b''"  


consts p1::program p2::program p3::program p4::program p5::program p6::program p7::program
definition "test = PROGRAM[ \<guillemotleft>p1\<guillemotright>; \<guillemotleft>p2\<guillemotright>; \<guillemotleft>p3\<guillemotright>; \<guillemotleft>p4\<guillemotright>; \<guillemotleft>p5\<guillemotright>; \<guillemotleft>p6\<guillemotright>; \<guillemotleft>p7\<guillemotright>; ]"

axiomatization 
  split_program :: "nat \<Rightarrow> nat \<Rightarrow> program \<Rightarrow> program \<Rightarrow> program"  and
  split_program_start :: "nat \<Rightarrow> program \<Rightarrow> program" and
  rev_program :: "nat \<Rightarrow> program \<Rightarrow> program"
where
  split_program_0 [simp]: "split_program 0 m p q = seq p (rev_program m q)"
and split_program_suc [simp]: "split_program (Suc n) m (seq p q) r = split_program n m p (seq q r)"
and split_program_start [simp]: "split_program_start n (program p) = program (split_program n n p Lang_Typed.skip)"
and split_program_start' [simp]: "split_program_start n p = (split_program n n p Lang_Typed.skip)"
and rev_program_suc [simp]: "rev_program (Suc (Suc n)) (seq p q) = seq p (rev_program (Suc n) q)"
and rev_program_1 [simp]: "rev_program (Suc 0) (seq p Lang_Typed.skip) = p"
and rev_program_0 [simp]: "rev_program 0 Lang_Typed.skip = Lang_Typed.skip"

lemma denotation_split: "denotation (split_program n m p q) = denotation (seq p q)"
  sorry  
  
fun mk_Suc :: "nat \<Rightarrow> nat" where
"mk_Suc 0 = 0" | "mk_Suc (Suc n) = Suc n"



lemma "split_program_start (mk_Suc 3) test = undefined"   
  unfolding test_def 
  apply simp
  

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

