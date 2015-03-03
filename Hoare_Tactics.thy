theory Hoare_Tactics
imports Hoare_Typed
begin

section {* Support lemmas for seq_tac *}

fun rev_program_untyped :: "program_rep \<Rightarrow> program_rep \<Rightarrow> program_rep" where
  "rev_program_untyped p (Seq q r) = rev_program_untyped (Seq p q) r"
| "rev_program_untyped p Skip = p"
| "rev_program_untyped p q = Seq p q"

lemma rev_program_untyped_denotation: "denotation_untyped (rev_program_untyped p q) = denotation_untyped (Seq p q)"
  by (induction q arbitrary: p, auto simp: denotation_untyped_assoc denotation_untyped_Skip[THEN ext])
lemma rev_program_untyped_welltyped: "well_typed p \<Longrightarrow> well_typed q \<Longrightarrow> well_typed (rev_program_untyped p q)"
  by (induction q arbitrary: p, auto)

fun split_program_untyped :: "nat \<Rightarrow> nat \<Rightarrow> program_rep \<Rightarrow> program_rep \<Rightarrow> program_rep" where
  "split_program_untyped 0 m p (Seq q r) = Seq p (rev_program_untyped q r)"
| "split_program_untyped 0 m p Skip = Seq p Skip"
| "split_program_untyped (Suc n) m (Seq p q) r = split_program_untyped n m p (Seq q r)"
| "split_program_untyped n m q r = Seq q r"


lemma split_program_untyped_denotation: "denotation_untyped (split_program_untyped n m p q) = denotation_untyped (Seq p q)"
  apply (rule split_program_untyped.induct[where P="\<lambda>n m p q. (denotation_untyped (split_program_untyped n m p q) = denotation_untyped (Seq p q))"])
  by (auto simp: rev_program_untyped_denotation denotation_untyped_assoc)
lemma split_program_untyped_welltyped: "well_typed p \<Longrightarrow> well_typed q \<Longrightarrow> well_typed (split_program_untyped n m p q)"
  apply (induction n arbitrary: p q)
  apply (case_tac q, auto simp: rev_program_untyped_welltyped)
  by (case_tac p, auto)
definition "rev_program p q = Abs_program (rev_program_untyped (Rep_program p) (Rep_program q))"
lemma rev_program_seq: "rev_program p (seq q r) == rev_program (seq p q) r"
  apply (rule eq_reflection)
  by (metis rev_program_def mk_untyped_seq rev_program_untyped.simps(1))
lemma rev_program_skip: "rev_program p Lang_Typed.skip == p"
  apply (rule eq_reflection)
  by (metis Rep_program_inverse mk_untyped_skip rev_program_def rev_program_untyped.simps(2)) 
  

definition "split_program n m p q = Abs_program (split_program_untyped n m (Rep_program p) (Rep_program q))"
lemma split_program_0_seq: "split_program 0 m p (seq q r) == seq p (rev_program q r)"
  unfolding split_program_def seq_def rev_program_def
  apply (subst Abs_program_inverse, auto)
  by (subst Abs_program_inverse, auto simp: rev_program_untyped_welltyped)
lemma split_program_0_skip: "split_program 0 m p Lang_Typed.skip == seq p Lang_Typed.skip"
  unfolding split_program_def mk_untyped_skip mk_untyped_seq seq_def by simp
lemma split_program_suc: "split_program (Suc n) m (seq p q) r == split_program n m p (seq q r)"
  unfolding split_program_def seq_def rev_program_def 
  apply (subst Abs_program_inverse, auto)
  by (subst Abs_program_inverse, auto)

definition "split_program_start n p == split_program n n p Lang_Typed.skip"

lemma denotation_split_program_start: "denotation (split_program_start n p) = denotation p"
  unfolding split_program_start_def denotation_def split_program_def seq_def mk_untyped_skip
  apply (subst Abs_program_inverse, auto simp: split_program_untyped_welltyped split_program_untyped_denotation)
  unfolding denotation_untyped_Seq[THEN ext] denotation_untyped_Skip[THEN ext]  
  by auto

lemmas split_program_simps = split_program_start_def split_program_0_seq split_program_0_skip split_program_suc rev_program_seq rev_program_skip

lemma insert_split: 
  fixes n
  assumes "hoare {P &m} \<guillemotleft>split_program_start n c\<guillemotright> {Q &m}"
  shows   "hoare {P &m} \<guillemotleft>c\<guillemotright> {Q &m}"
apply (rule denotation_eq_rule)
apply (fact denotation_split_program_start[symmetric])
by (fact assms)

section {* Tactic/method declarations *}

ML_file "hoare_tactics.ML"

method_setup wp = {* Scan.succeed (fn ctx => (SIMPLE_METHOD' (Hoare_Tactics.wp_tac ctx))) *} "weakest precondition (tail of program: if + assign + skip)"
method_setup wp1 = {* Scan.succeed (fn ctx => (SIMPLE_METHOD' (Hoare_Tactics.wp1_tac ctx))) *} "weakest precondition (last statement only)"
method_setup skip = {* Scan.succeed (K (SIMPLE_METHOD' Hoare_Tactics.skip_tac)) *} "skip"
(* TODO: make test cases *)
ML {* Markup.completion *}

ML {*
val arg_parse_assertion = 
  Scan.peek (Args.named_term o 
  (fn ctx => fn str => ((writeln (String.implode ( (map (fn x => if Char.ord x<20 then #"~" else x) (String.explode str))))); 
Syntax.read_term ctx ("ASSERTION["^str^"]"))) o 
  Context.proof_of)
*}

method_setup seq = {*
 (Scan.lift Parse.int -- 
  Scan.option (Scan.lift (Args.$$$ "invariant" |-- Args.colon) |-- Scan.lift Parse.string))
  >> (fn (n,inv) => fn ctx => (SIMPLE_METHOD' (Hoare_Tactics.seq_tac ctx n 
(case inv of NONE => NONE | SOME str => SOME (Syntax.read_term ctx ("ASSERTION["^str^"]::bool")))
))) *} "seq n [invariant: term]"

(* TODO:

- conseq
- exfalso
- elim*
- seq
- sp
- wp n
- rnd
- if
- while
- call
- proc
- proc*
- swap


*)

end

