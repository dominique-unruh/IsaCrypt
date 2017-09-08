theory Wlog
imports Main
keywords "wlog" :: "prf_script" and "goal" :: "prf_script"
begin


ML_file "wlog.ML"

(* lemma assumes "X \<Longrightarrow> Y"  and "\<not> X \<Longrightarrow> Y" shows "Y" *)
  


lemma "a*a \<ge> (0::int)"
proof -
  have true: "a=a" ..
 (*  presume hypothesis: "0 \<le> a \<Longrightarrow> a=a \<Longrightarrow> 0 \<le> a * a" for a::int
  (* presume not_already: "\<not>(0\<le>a)" *)
  show ?thesis (*if not_already: "\<not>(0\<le>a)"*)
    apply (cases "0\<le>a")
    apply (rule hypothesis)
    apply (assumption)
  proof -
    assume "\<not> (0\<le>a)"
    hence "a < 0" by simp
    hence "- a \<ge> 0" by simp
    hence "0 \<le> - a * - a" by (rule hypothesis, simp) 
    thus "0 \<le> a*a" by simp
  qed

next

  fix a::int 
  goal "a*a\<ge>0" *)


  wlog geq0: "a\<ge>0" for a assumes true
  proof -
    from negation 
    have "a < 0" by simp
    hence "- a \<ge> 0" by simp
    thm hypothesis
    hence "0 \<le> - a * - a" apply (rule hypothesis) by simp
    thus "0 \<le> a*a" by simp
  qed

  from geq0 show ?thesis by simp
qed


lemma
  fixes a b :: nat
  assumes bla: "True"
  assumes neq: "a \<noteq> b"
  shows "a+b \<ge> 1" (is ?th) and "a+b \<ge> 0"
proof -
  goal "a+b \<ge> 1"
  (* goal "?thesis" (is "a+b \<ge> 1") *)
  have neq2: "a>b\<or>b>a" using neq bla by auto 
  have comm: "1 \<le> a + b \<Longrightarrow> 1 \<le> b + a" for a b :: nat by auto

  let ?a = a

  have test[]: "\<And>a. b \<noteq> a \<Longrightarrow> a \<noteq> b \<Longrightarrow> 1 \<le> a + b" sorry

  print_commands

  wlog neq3: "b\<noteq>a" for a assumes neq
  proof (cases rule:hypothesis[where a=a]) print_cases
    case neq show ?case using assms(2) by blast 
    case neq3 show ?case using assms(2) by blast 
  qed

  have aux: "P \<Longrightarrow> (P \<Longrightarrow> Q) \<Longrightarrow> Q" for P Q by metis

  wlog geq: "a > b" for a b assumes neq3
  proof (cases "a>b")
  case True show ?thesis using True hypothesis by blast
  next case False show ?thesis proof (rule aux, cases rule:hypothesis[of a b])
    case geq show ?case using False neq2 by blast
    next case neq3 show ?case using neq2 by auto
    next assume "1 \<le> b + a" then show "1 \<le> a + b" by linarith
    qed
  qed

  note assms = neq neq3 

  have "b<a\<or>a<b" by (simp add: geq)

 (* apply (tactic \<open>resolve_tac @{context} [neq2'] 1\<close>) using assms by auto *)

  wlog tmp: "a=a" for a b assumes geq 
    using hypothesis neq geq by metis

  from geq have "a \<ge> 1" by auto

  then show "1 \<le> a + b" by auto
next
  goal "a+b \<ge> 0"
  show ?thesis by auto
qed
