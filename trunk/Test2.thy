(* Written by Dominique Unruh *)
theory Test2
imports Main
begin

section "Implementation of module-simplifier"


definition fun_equiv :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where "fun_equiv f x y == f x = f y"
lemma fun_equiv_refl: "fun_equiv f x x" by(simp add: fun_equiv_def)

ML {*
(* Call as: hoare_simproc_tac (simplifications@congruences) context/simpset *)
fun fun_equiv_simproc_tac intros ctxt =
  SUBGOAL (fn (goal,i) =>
    case goal of
      Const(@{const_name Trueprop},_) $ (Const(@{const_name fun_equiv},_)$_$_$_) => 
        (resolve0_tac intros THEN_ALL_NEW fun_equiv_simproc_tac intros ctxt) i
        ORELSE (rtac @{thm fun_equiv_refl} i)
    | _ => 
        SOLVED' (simp_tac ctxt) i)

fun fun_equiv_simproc start intros _ ctxt (t:cterm) = 
  let val fresh_var = Var(("x",Term.maxidx_of_term (Thm.term_of t)+1),Thm.typ_of_cterm t)
      val goal = Logic.mk_equals (Thm.term_of t,fresh_var)
      val thm = Goal.prove ctxt [] [] goal 
                (fn {context,...} => resolve0_tac start 1 THEN ALLGOALS (fun_equiv_simproc_tac intros context))
  in 
    if (Thm.rhs_of thm) aconvc t then NONE else SOME thm
  end
  handle ERROR msg => (warning ("fun_equiv_simproc failed\nTerm was:\n"^(@{make_string} t)^"\nError: "^msg); NONE)

fun fun_equiv_simproc_named start cong simp morph ctxt =
  fun_equiv_simproc (Named_Theorems.get ctxt start) (Named_Theorems.get ctxt simp @ Named_Theorems.get ctxt cong) morph ctxt
*}

section "Minimal Hoare logic"

(* A simple language and Hoare logic *)
typedecl program
typedecl memory
consts
  seq :: "program \<Rightarrow> program \<Rightarrow> program" (infixl ";" 100) (* c;d: run c, then run d *)
  ifthen :: "(memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> program" (* ifthen e c: run c if e(current_mem)=true *)
  while :: "(memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> program" (* while e c: run c while e(current_mem)=true *)
  denotation :: "program \<Rightarrow> memory \<Rightarrow> memory"  (* denotation c m: memory after running c, when starting with memory m *)
  hoare :: "(memory \<Rightarrow> bool) \<Rightarrow> program \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> bool" 
      (* hoare P c Q: if P(current_mem), then after running c, we have Q(current_mem) *)

section "Instantiating the simplifier"

named_theorems denot_simp_start
named_theorems denot_simp
named_theorems denot_cong

lemma hoare_cong_start [denot_simp_start]: "fun_equiv denotation c c' \<Longrightarrow> hoare P c Q == hoare P c' Q" sorry
lemma while_cong [denot_cong]: "fun_equiv denotation c c' \<Longrightarrow> fun_equiv denotation (while b c) (while b c')" sorry
lemma seq_cong [denot_cong]: "fun_equiv denotation a a' \<Longrightarrow> fun_equiv denotation b b' \<Longrightarrow> fun_equiv denotation (a ; b) (a' ; b')" sorry
lemma if_cong [denot_cong]: "fun_equiv denotation c c' \<Longrightarrow> fun_equiv denotation (ifthen b c) (ifthen b c')" sorry
lemma seq_assoc [denot_simp]: "fun_equiv denotation (a ; (b ; c)) (a; b; c)" sorry
lemma ifthen_true [denot_simp]: "(\<And>m. e m) \<Longrightarrow> fun_equiv denotation (ifthen e c) c" sorry
lemma double_while [denot_simp]: "(\<And>m. e m = e' m) \<Longrightarrow> fun_equiv denotation c d \<Longrightarrow> fun_equiv denotation (seq (while e c) (while e' d)) (while e c)" sorry

(* -- "If the set of simplification theorems is fixed, we can use the following setup"
  lemmas hoare_congruences = while_cong if_cong seq_cong
  lemmas hoare_simps = ifthen_true seq_assoc double_while
  simproc_setup hoare_simproc ("hoare P c Q") = {* fun_equiv_simproc @{thms hoare_cong_start} @{thms hoare_simps hoare_congruences} *}
*)


(* To make use of dynamic lists of theorems, we use the following setup *)
simproc_setup hoare_simproc ("hoare P c Q") = {* 
  fun_equiv_simproc_named @{named_theorems denot_simp_start}
                          @{named_theorems denot_cong}
                          @{named_theorems denot_simp}
*}

section "Tests"

(* Testing the simplifier rules *)
lemma
  assumes "hoare P (while e (a;b;c)) Q"
  shows "hoare P (while e (a;(b;c))) Q \<and> True"
using assms 
by simp

lemma 
  assumes "hoare P (while P (c;d;e)) Q"
  assumes "\<And>x. P x = R x"
  shows "hoare P ((while P (c;(d;e))); (while R ((c;d);e))) Q"
using assms by simp

lemma
  assumes "\<And>x. Q x"
  assumes "hoare (\<lambda>m. P x \<and> Q x) (while P (c;(d;e);(f;g);c)) (\<lambda>m. m=m)"
  shows "hoare (\<lambda>m. P x) (while P (c;(d;e);ifthen (\<lambda>m. m=m) (f;g;c))) (\<lambda>m. True)"
using assms by simp

(* Test: Disabling the simproc *)
lemma
  assumes "hoare P (a;(b;c)) Q"
  shows   "hoare P (a;(b;c)) Q \<and> True"
using[[simproc del: hoare_simproc]] -- "Without this, proof fails"
apply simp
by (fact assms)
end
