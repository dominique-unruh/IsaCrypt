theory Test
imports Main
begin

section "Minimal Hoare logic"

(* A simple language and Hoare logic *)
typedecl program
typedecl memory
consts
  seq :: "program \<Rightarrow> program \<Rightarrow> program" (infixl ";" 10) (* c;d: run c, then run d *)
  ifthen :: "(memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> program" (* ifthen e c: run c if e(current_mem)=true *)
  while :: "(memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> program" (* while e c: run c while e(current_mem)=true *)
  denotation :: "program \<Rightarrow> memory \<Rightarrow> memory"  (* denotation c m: memory after running c, when starting with memory m *)
  hoare :: "(memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> bool" 
      (* hoare P c Q: if P(current_mem), then after running c, we have Q(current_mem) *)

(* seq is associative modulo denotational equivalence.
  Thus we should be able to rewrite "a;(b;c)" to "a;b;c"
  within a hoare triple. E.g., the following should be solved with simp: *)
lemma
  assumes "hoare P (while e (a;b;c)) Q"
  shows "hoare P (while e (a;(b;c))) Q"
using assms
oops (* by simp *)

section "A failed attempt"

experiment begin
(* Here a natural approach first which, however, fails. *)

(* A congruence rule for the simplifier. 
   To rewrite a hoare triple "hoare P c Q", 
   we need to rewrite "denotation c". *)

lemma enter [cong]:
  assumes "P==P'" and "Q==Q'"
  assumes "denotation c == denotation c'"
  shows "hoare P c Q == hoare P' c' Q'"
sorry

(* To descend further into subterms, we need a congruence-rule for while. *)
lemma while [cong]: 
  assumes "e=e'"
  and "denotation c == denotation c'"
  shows "denotation (while e c) \<equiv> denotation (while e' c')"
sorry

(* And we give a simplification rule for the associativity of seq *)
lemma assoc [simp]:
  "denotation (a;(b;c)) = denotation (a;b;c)"
sorry

(* Now we can simplify the lemma from above *)
lemma
  assumes "hoare P (while e (a;b;c)) Q"
  shows "hoare P (while e (a;(b;c))) Q"
using assms by simp

(* Unfortunately, this does not work any more once we add more congruence rules. *)
(* To descend further into subterms, we need a congruence-rule for while. *)
lemma ifthen [cong]: 
  assumes "e=e'"
  and "denotation c == denotation c'"
  shows "denotation (ifthen e c) \<equiv> denotation (ifthen e' c')"
sorry
(* Warning: Overwriting congruence rule for "Test.denotation" *)

(* Simplifier doesn't work any more because the congruence rule for while was overwritten *)
lemma
  assumes "hoare P (while e (a;b;c)) Q"
  shows "hoare P (while e (a;(b;c))) Q"
using assms 
oops (* by simp *)

end

section {* A working attempt *}

(* Define copies of the denotation-constant, to control the simplifier *)
definition "denotation_simp == denotation"
definition "denotation_done == denotation"

(* A congruence rule for the simplifier. 
   To rewrite a hoare triple "hoare P c Q", 
   we need to rewrite "denotation c".

   This means, the congruence rule should have an assumption
   "denotation c == denotation c'"

   However, to avoid infinite loops with the rewrite rules below,
   we use the logically equivalent assumption
   "denotation_simp c == denotation_done c'"

   This means that we need to configure the rules below rewrite
   "denotation_simp c" into "denotation_done c'" where c' is 
   the simplication of c (module denotational equivalence).
 *)
lemma enter [cong]:
  assumes "P==P'" and "Q==Q'"
  assumes "denotation_simp c == denotation_done c'"
  shows "hoare P c Q == hoare P' c' Q'"
sorry

(* A similar congruence rule for simplifying expressions
  of the form "denotation c". *)
lemma denot [cong]:
  assumes "denotation_simp c == denotation_done c'"
  shows "denotation c == denotation c'"
sorry

(* Now we add a congruence-rule for while.
  Since we saw above that we cannot use several congruence-rules
  with "denotation" as their head,
  we simulate a congruence rule using a simp-rule.
  
  To rewrite "denotation_simp (while e c)", we need to rewrite
  "denotation_simp c".

  We put denotation_done on the rhs instead of denotation_simp 
  to avoid infinite loops.
*)
lemma while [simp]: 
  assumes "e=e'"
  and "denotation_simp c == denotation_done c'"
  shows "denotation_simp (while e c) \<equiv> denotation_done (while e' c')"
sorry

(* A pseudo-congruence rule for ifthen *)
lemma ifthen [simp]:
  assumes "e=e'"
  and "denotation_simp c == denotation_done c'"
  shows "denotation_simp (ifthen e c) == denotation_done (ifthen e' c')"
sorry

(* A pseudo-congruence rule for seq *)
lemma seq [simp]:
  assumes "denotation_simp c == denotation_done c'"
  and "denotation_simp d == denotation_done d'"
  shows "denotation_simp (c;d) == denotation_done (c';d')"
sorry

(* Finally, we can state associativity of seq. *)
lemma assoc [simp]:
  "denotation_simp (a;(b;c)) = denotation_simp (a;b;c)"
sorry

(* Finally, since our congruence-rules expect the rewriting to rewrite
  "denotation_simp c" into "denotation_done c'", 
  we need to translate any non-rewritten "denotation_simp" into
  "denotation_done".

  However, a rule "denotation_simp c == denotation_done c" does not work,
  because it could be triggered too early, and block the pseudo-congruence rules above.
  
  So we only trigger the rule when the current term would not match
  any of the pseudo congruence rules *)
lemma finish [simp]: 
  assumes "NO_MATCH (while e1 c1) a"
  assumes "NO_MATCH (ifthen e2 c2) a"
  assumes "NO_MATCH (c3;d3) a"
  shows "denotation_simp a = denotation_done a"
sorry

(* Testing the simplifier rules *)
lemma
  assumes "hoare P (while e (a;b;c)) Q"
  shows "hoare P (while e (a;(b;c))) Q"
using assms 
by simp


(* Some more complex test *)
lemma iftrue [simp]: "denotation_simp (ifthen (\<lambda>m. True) c) == denotation_simp c" sorry
lemma
  assumes "\<And>x. Q x"
  assumes "hoare (\<lambda>m. P x \<and> Q x) (while P (c;(d;e);(f;g);c)) (\<lambda>m. m=m)"
  shows "hoare (\<lambda>m. P x) (while P (c;(d;e);ifthen (\<lambda>m. m=m) (f;g;c))) (\<lambda>m. True)"
using assms
apply simp (* Hmm. Only partially simplified... The assoc rule is not applied to the result of the iftrue rule *)
by simp (* Rerunning simp solves the goal *)
(* By the way: "using assms by auto" solves the goal in one go *)

end
