theory Procedures
imports Lang_Untyped "~~/src/HOL/Proofs/Lambda/StrongNorm"
begin

fun nth_opt :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "nth_opt (x#xs) 0 = Some x"
| "nth_opt (x#xs) (Suc n) = nth_opt xs n"
| "nth_opt [] _ = None"

lemma nth_opt_prefix: "nth_opt F n = Some T \<Longrightarrow> nth_opt (F @ E) n = Some T"
  apply (induction F arbitrary: n, auto)
  by (case_tac n, auto)
lemma nth_opt_len: "nth_opt F n = Some T \<Longrightarrow> length F > n"
  apply (induct F arbitrary: n, simp)
  by (case_tac n, auto)

datatype procedure_type_open = ProcSimple procedure_type | ProcFun procedure_type_open procedure_type_open
fun ProcFun' where
  "ProcFun' [] T = T"
| "ProcFun' (T#Ts) U = ProcFun T (ProcFun' Ts U)"

inductive well_typed'' :: "procedure_type_open list \<Rightarrow> program_rep \<Rightarrow> bool"
and well_typed_proc'' :: "procedure_type_open list \<Rightarrow> procedure_rep \<Rightarrow> procedure_type_open \<Rightarrow> bool" where
  wt_Seq: "well_typed'' E p1 \<and> well_typed'' E p2 \<Longrightarrow> well_typed'' E (Seq p1 p2)"
| wt_Assign: "eu_type e = vu_type v \<Longrightarrow> well_typed'' E (Assign v e)"
| wt_Sample: "ed_type e = vu_type v \<Longrightarrow> well_typed'' E (Sample v e)"
| wt_Skip: "well_typed'' E Skip"
| wt_While: "eu_type e = bool_type \<Longrightarrow> well_typed'' E p \<Longrightarrow> well_typed'' E (While e p)"
| wt_IfTE: "eu_type e = bool_type \<Longrightarrow> well_typed'' E thn \<Longrightarrow>  well_typed'' E els \<Longrightarrow> well_typed'' E (IfTE e thn els)"
| wt_CallProc: "well_typed_proc'' E prc (ProcSimple \<lparr> pt_argtypes=map eu_type args, pt_returntype=vu_type v \<rparr>) \<Longrightarrow>
   well_typed'' E (CallProc v prc args)"
| wt_Proc: "well_typed'' E body \<Longrightarrow>
   list_all (\<lambda>v. \<not> vu_global v) pargs \<Longrightarrow>
   distinct pargs \<Longrightarrow>
   well_typed_proc'' E (Proc body pargs ret) (ProcSimple \<lparr> pt_argtypes=map vu_type pargs, pt_returntype=eu_type ret\<rparr>)"
| wt_ProcRef: "nth_opt E i = Some T \<Longrightarrow> well_typed_proc'' E (ProcRef i) T"
| wt_ProcAppl: "well_typed_proc'' E p (ProcFun T U) \<Longrightarrow>
  well_typed_proc'' E q T \<Longrightarrow>
  well_typed_proc'' E (ProcAppl p q) U"
| wt_ProcAbs: "well_typed_proc'' (T#E) p U \<Longrightarrow> well_typed_proc'' E (ProcAbs p) (ProcFun T U)"
lemma wt_Assign_iff: "eu_type e = vu_type v = well_typed'' E (Assign v e)"
  apply (rule iffI, simp add: wt_Assign)
  by (cases rule:well_typed''.cases, auto)
lemma wt_Seq_iff: "(well_typed'' E p1 \<and> well_typed'' E p2) = well_typed'' E (Seq p1 p2)"
  apply (rule iffI, simp add: wt_Seq)
  by (cases rule:well_typed''.cases, auto)
lemma wt_Sample_iff: "(ed_type e = vu_type v) = well_typed'' E (Sample v e)"
  apply (rule iffI, simp add: wt_Sample)
  by (cases rule:well_typed''.cases, auto)
lemma wt_While_iff: "(eu_type e = bool_type \<and> well_typed'' E p) = well_typed'' E (While e p)"
  apply (rule iffI, simp add: wt_While)
  by (cases rule:well_typed''.cases, auto)
lemma wt_IfTE_iff: "(eu_type e = bool_type \<and> well_typed'' E thn \<and>  well_typed'' E els) = well_typed'' E (IfTE e thn els)"
  apply (rule iffI, simp add: wt_IfTE)
  by (cases rule:well_typed''.cases, auto)
lemma wt_CallProc_iff: "
   well_typed_proc'' E prc (ProcSimple \<lparr> pt_argtypes=map eu_type args, pt_returntype=vu_type v\<rparr>) =
   well_typed'' E (CallProc v prc args)"
  apply (rule iffI, auto simp: wt_CallProc)
  by (cases rule:well_typed''.cases, auto)
lemma wt_Proc_iff: "
  (T'=ProcSimple \<lparr> pt_argtypes=map vu_type pargs, pt_returntype=eu_type ret\<rparr> \<and> 
   well_typed'' E body \<and>
   list_all (\<lambda>v. \<not> vu_global v) pargs \<and>
   distinct pargs) =
   well_typed_proc'' E (Proc body pargs ret) T'"
  apply (rule iffI, simp add: wt_Proc)
  by (cases rule:well_typed_proc''.cases, auto)
lemma wt_ProcRef_iff: "(nth_opt E i = Some T) = well_typed_proc'' E (ProcRef i) T"
  apply (rule iffI, simp add: wt_ProcRef)
  by (cases rule:well_typed_proc''.cases, auto)
lemma wt_ProcAppl_iff: "(\<exists>T. well_typed_proc'' E p (ProcFun T U) \<and>
  well_typed_proc'' E q T) =
  well_typed_proc'' E (ProcAppl p q) U"
  apply (rule iffI, auto simp: wt_ProcAppl)
  by (cases rule:well_typed_proc''.cases, auto)
lemma wt_ProcAbs_iff: "(\<exists>T U. TU = ProcFun T U \<and> well_typed_proc'' (T#E) p U) = well_typed_proc'' E (ProcAbs p) TU"
  apply (rule iffI, auto simp: wt_ProcAbs)
  by (cases rule:well_typed_proc''.cases, auto)

fun lift_proc_in_prog :: "[program_rep, nat] \<Rightarrow> program_rep"
and lift_proc :: "[procedure_rep, nat] \<Rightarrow> procedure_rep" where
  "lift_proc_in_prog Skip i = Skip"
| "lift_proc_in_prog (Assign v e) i = Assign v e"
| "lift_proc_in_prog (Sample v e) i = Sample v e"
| "lift_proc_in_prog (Seq p1 p2) i = Seq (lift_proc_in_prog p1 i) (lift_proc_in_prog p2 i)"
| "lift_proc_in_prog (IfTE c p1 p2) i = IfTE c (lift_proc_in_prog p1 i) (lift_proc_in_prog p2 i)"
| "lift_proc_in_prog (While c p1) i = While c (lift_proc_in_prog p1 i)"
| "lift_proc_in_prog (CallProc v p a) i = CallProc v (lift_proc p i) a"
| "lift_proc (Proc body args ret) i = Proc (lift_proc_in_prog body i) args ret"
| "lift_proc (ProcRef i) k = (if i < k then ProcRef i else ProcRef (Suc i))"
| "lift_proc (ProcAppl s t) k = ProcAppl (lift_proc s k) (lift_proc t k)"
| "lift_proc (ProcAbs s) k = ProcAbs (lift_proc s (Suc k))"

fun subst_proc_in_prog :: "[nat, procedure_rep, program_rep] \<Rightarrow> program_rep"
and subst_proc :: "[nat, procedure_rep, procedure_rep] \<Rightarrow> procedure_rep"
where
  subst_proc_Skip: "subst_proc_in_prog i p Skip = Skip"
| subst_proc_Seq: "subst_proc_in_prog i p (Seq c1 c2) = Seq (subst_proc_in_prog i p c1) (subst_proc_in_prog i p c2)"
| subst_proc_Assign: "subst_proc_in_prog i p (Assign v e) = Assign v e"
| subst_proc_Sample: "subst_proc_in_prog i p (Sample v e) = Sample v e"
| subst_proc_IfTE: "subst_proc_in_prog i p (IfTE e c1 c2) = IfTE e (subst_proc_in_prog i p c1) (subst_proc_in_prog i p c2)"
| subst_proc_While: "subst_proc_in_prog i p (While e c) = While e (subst_proc_in_prog i p c)"
| subst_proc_CallProc: "subst_proc_in_prog i p (CallProc v p' args) = CallProc v (subst_proc i p p') args"
| subst_proc_Proc: "subst_proc i p (Proc body args ret) =
     Proc (subst_proc_in_prog i p body) args ret"
| subst_proc_ProcRef: "subst_proc k s (ProcRef i) = 
      (if k < i then ProcRef (i - 1) else if i=k then s else ProcRef i)"
| subst_proc_ProcAppl: "subst_proc k s (ProcAppl t u) = ProcAppl (subst_proc k s t) (subst_proc k s u)"
| subst_proc_ProcAbs: "subst_proc k s (ProcAbs t) = ProcAbs (subst_proc (Suc k) (lift_proc s 0) t)"


function (sequential,domintros) beta_reduce_prog :: "program_rep \<Rightarrow> program_rep"
and beta_reduce_proc :: "procedure_rep \<Rightarrow> procedure_rep" where
  "beta_reduce_prog Skip = Skip"
| "beta_reduce_prog (Seq p1 p2) = Seq (beta_reduce_prog p1) (beta_reduce_prog p2)"
| "beta_reduce_prog (CallProc v p e) = CallProc v (beta_reduce_proc p) e"
| "beta_reduce_proc (Proc body args ret) = Proc (beta_reduce_prog body) args ret"
| "beta_reduce_proc (ProcAppl p q) = 
      (case beta_reduce_proc p of ProcAbs p' \<Rightarrow> beta_reduce_proc (subst_proc 0 q p')
          | p' \<Rightarrow> ProcAppl p' (beta_reduce_proc q))"
| "beta_reduce_proc (ProcAbs p) = ProcAbs (beta_reduce_proc p)"
by pat_completeness auto

ML {* @{term beta_reduce_prog_beta_reduce_proc_dom} *}

locale open_proc_termination begin


(*

Mapping proc to dB:
 ProcRef i \<rightarrow> Var i
 ProcAppl \<rightarrow> App
 ProcAbs \<rightarrow> Abs
 Proc p \<rightarrow> p
 Assign \<rightarrow> (\<lambda>x. x) : Atom0\<rightarrow>Atom0
 Seq p q \<rightarrow> (\<lambda>x y. x) p q : (Atom0\<rightarrow>Atom0)\<rightarrow>(Atom0\<rightarrow>Atom0)\<rightarrow>(Atom0\<rightarrow>Atom0)
 CallProc p \<rightarrow> p
*)

abbreviation "Proc0 == Abs(Var 0)"
abbreviation "Proc1 == Abs(Var 0)"
abbreviation "Proc2 == Abs(Abs(Var 0))"

fun prog_to_dB :: "program_rep \<Rightarrow> dB" and proc_to_dB :: "procedure_rep \<Rightarrow> dB" where
  "prog_to_dB Skip = Proc0"
| "prog_to_dB (Assign v e) = Proc0"
| "prog_to_dB (Sample v e) = Proc0"
| "prog_to_dB (IfTE e p q) = Proc2 \<degree> prog_to_dB p \<degree> prog_to_dB q"
| "prog_to_dB (Seq p q) = Proc2 \<degree> prog_to_dB p \<degree> prog_to_dB q"
| "prog_to_dB (While e p) = Proc1 \<degree> prog_to_dB p"
| "prog_to_dB (CallProc v p a) = Proc1 \<degree> proc_to_dB p"
| "proc_to_dB (Proc p ret args) = Proc1 \<degree> prog_to_dB p"
| "proc_to_dB (ProcRef i) = Var i"
| "proc_to_dB (ProcAbs p) = Abs (proc_to_dB p)"
| "proc_to_dB (ProcAppl p q) = proc_to_dB p \<degree> proc_to_dB q"

lemma proc_to_dB_lift [iff]:
 shows "prog_to_dB (lift_proc_in_prog p k) = lift (prog_to_dB p) k"
 and   "proc_to_dB (lift_proc q k) = lift (proc_to_dB q) k"
by (induction rule:lift_proc_in_prog_lift_proc.induct, auto)

lemma proc_to_dB_subst [iff]:
 shows "prog_to_dB (subst_proc_in_prog k x p) = prog_to_dB p[proc_to_dB x/k]"
 and   "proc_to_dB (subst_proc k x q) = proc_to_dB q[proc_to_dB x/k]"
by (induction p and q arbitrary: k x and k x, auto)

fun to_dB where
  "to_dB (Inl p) = prog_to_dB p"
| "to_dB (Inr p) = proc_to_dB p"

(*
proc_type_open \<rightarrow> lambda type:
 ProcSimple \<rightarrow> Atom0\<rightarrow>Atom0
 ProcFun p q \<rightarrow> p q
*)
abbreviation "ProcT == Fun (Atom 0) (Atom 0)"

fun typ_conv :: "procedure_type_open \<Rightarrow> type" where
  "typ_conv (ProcSimple _) = ProcT"
| "typ_conv (ProcFun T U) = Fun (typ_conv T) (typ_conv U)"

lemma typ_pres:
  shows "well_typed'' E pg \<Longrightarrow> (\<lambda>i. typ_conv (E!i)) \<turnstile> prog_to_dB pg : ProcT"
  and   "well_typed_proc'' E p T \<Longrightarrow>(\<lambda>i. typ_conv (E!i)) \<turnstile> proc_to_dB p : typ_conv T"
proof (induction E pg and E p T rule:well_typed''_well_typed_proc''.inducts)
case (wt_ProcRef E i T) thus ?case
  apply auto
  apply (induct E arbitrary: i, auto)
  by (metis fact_nat.cases nth_Cons_0 nth_Cons_Suc nth_opt.simps(1) nth_opt.simps(2) option.inject)
next case (wt_ProcAbs T E p U) show ?case apply auto 
  apply (rule rev_iffD1[OF wt_ProcAbs.IH])
  apply (tactic "cong_tac 1")+
  by (auto simp: shift_def)
qed auto

inductive subterm :: "dB \<Rightarrow> dB \<Rightarrow> bool" where
  srefl [simp]: "subterm t t"
| sapp1: "subterm t t' \<Longrightarrow> subterm t (t'\<degree>u)"
| sapp2: "subterm t t' \<Longrightarrow> subterm t (u\<degree>t')"
| sabs: "subterm t t' \<Longrightarrow> subterm t (Abs t')"

(*
a\<longrightarrow>b := \<exists>C. a \<rightarrow>\<beta> C[b] \<or> a=C[b]  (but not a=b)
*)
inductive BETA :: "dB \<Rightarrow> dB \<Rightarrow> bool" (infixl "\<leadsto>" 50) where
  step: "subterm a a' \<Longrightarrow> a' \<rightarrow>\<^sub>\<beta> b \<Longrightarrow> a\<leadsto>b"
| sub: "subterm b a \<Longrightarrow> a\<noteq>b \<Longrightarrow> a\<leadsto>b"

abbreviation "beta_rel == beta_reduce_prog_beta_reduce_proc_rel"
abbreviation "beta_dom == beta_reduce_prog_beta_reduce_proc_dom"
abbreviation "beta_reduce_prog_dom x == beta_reduce_prog_beta_reduce_proc_dom(Inl x)"
abbreviation "beta_reduce_proc_dom x == beta_reduce_prog_beta_reduce_proc_dom(Inr x)"
abbreviation "beta_reduce == beta_reduce_prog_beta_reduce_proc_sumC"

thm beta_reduce_prog_beta_reduce_proc_rel.induct

thm_deps IT_implies_termi
unused_thms

lemma
  assumes termip: "termip beta a"
  assumes subterm: "subterm (to_dB A) a"
  shows "beta_dom A \<and> to_dB A \<rightarrow>\<^sub>\<beta>\<^sup>* to_dB (beta_reduce A)"
apply (insert subterm) using termip apply (induction arbitrary: A, simp)
    

(* Lemma: a \<rightarrow>\<beta> b \<Longrightarrow> a \<leadsto> b *)
lemma
  assumes "beta_rel b a"
  assumes "beta_dom b"
  shows "to_dB a \<leadsto> to_dB b"
proof -
have size_neq: "\<And>a b. size a \<noteq> size b \<Longrightarrow> a \<noteq> b" by auto
show "to_dB a \<leadsto> to_dB b"
proof (insert assms, induction rule:beta_reduce_prog_beta_reduce_proc_rel.induct) 
fix p1 p2
show "to_dB (Inl (Seq p1 p2)) \<leadsto> to_dB (Inl p1)"
  apply (rule sub, simp, rule sapp1, rule sapp2, simp)
  by (simp, rule size_neq, simp)
next fix p1 p2
show "to_dB (Inl (Seq p1 p2)) \<leadsto> to_dB (Inl p2)"
  apply (rule sub, simp, rule sapp2, rule srefl)
  by (simp, rule size_neq, simp)
next fix v p e
show "to_dB (Inl (CallProc v p e)) \<leadsto> to_dB (Inr p)"
  apply (rule sub, simp_all) apply (rule sapp2) apply (rule srefl)
  by (rule size_neq, simp)
next fix body ret args
show "to_dB (Inr (Proc body args ret)) \<leadsto> to_dB (Inl body)"
  apply (rule sub, simp_all) apply (rule sapp2) apply (rule srefl)
  by (rule size_neq, simp)
next fix p q
show "to_dB (Inr (ProcAppl p q)) \<leadsto> to_dB (Inr p)"
  apply (rule sub, simp_all) apply (rule sapp1) apply (rule srefl)
  by (rule size_neq, simp)
next fix p q
show "to_dB (Inr (ProcAppl p q)) \<leadsto> to_dB (Inr q)"
  apply (rule sub, simp_all) apply (rule sapp2) apply (rule srefl)
  by (rule size_neq, simp)
next fix p q i
show "to_dB (Inr (ProcAppl p q)) \<leadsto> to_dB (Inr q)"
  apply (rule sub, simp_all) apply (rule sapp2) apply (rule srefl)
  by (rule size_neq, simp)
next fix p q x
assume "projr (beta_reduce_prog_beta_reduce_proc_sumC (Inr p)) = ProcAbs x"
show "to_dB (Inr (ProcAppl p q)) \<leadsto> to_dB (Inr (subst_proc 0 q x))"
  apply (rule step, simp_all) apply (rule srefl) 
  apply (rule beta.intros)
  
  by (rule size_neq, simp)

(*

\<rightarrow>\<delta> (our dom-relation)
\<rightarrow>\<beta> (beta from dB)

a \<rightarrow>\<delta> b \<rightarrow>\<delta> c \<rightarrow>\<delta> d
\<Longrightarrow>
a \<rightarrow>\<beta> C[b]\<rightarrow>C[C'[c]\<rightarrow>C[C'[C''[d]]]

a\<longrightarrow>b := \<exists>C. a \<rightarrow>\<beta> C[b] \<or> a=C[b]  (but not a=b)

Lemma: a \<rightarrow>\<beta> b \<Longrightarrow> a \<longrightarrow> b

Lemma: a \<longrightarrow> b \<Longrightarrow> a (\<rightarrow>\<beta> <*lex*> size) b

Lemma: well_typed \<Longrightarrow> acc (\<rightarrow>\<beta> <*lex*> size) 

*)


end
end

declare [[syntax_ambiguity_warning = false]]
(* Restore syntax TODO *)
