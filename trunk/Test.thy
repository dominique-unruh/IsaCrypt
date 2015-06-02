theory Test
imports Main Tools
begin

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


(* To make use of dynamic lists of theorems, we use the following setup *)
simproc_setup hoare_simproc ("hoare P c Q") = {* 
  Tools.fun_equiv_simproc_named @{named_theorems denot_simp_start}
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
