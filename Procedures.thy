theory Procedures
imports "~~/src/HOL/Proofs/Lambda/Commutation" "~~/src/HOL/Proofs/Lambda/StrongNorm" Lang_Untyped 
begin

subsection {* Various facts and definitions *}

definition "freshvar vs = (SOME vn. \<forall>v\<in>set vs. vn \<noteq> vu_name v)"
lemma freshvar_global: "mk_variable_untyped (Variable (freshvar vs)) \<notin> set vs"
  sorry
lemma freshvar_local: "mk_variable_untyped (LVariable (freshvar vs)) \<notin> set vs"
  sorry

fun fresh_variables_local :: "variable_untyped list \<Rightarrow> type list \<Rightarrow> variable_untyped list" where
  "fresh_variables_local used [] = []"
| "fresh_variables_local used (t#ts) =
    (let vn=freshvar used in 
     let v=\<lparr> vu_name=vn, vu_type=t, vu_global=False \<rparr> in
     v#fresh_variables_local (v#used) ts)"
lemma fresh_variables_local_distinct: "distinct (fresh_variables_local used ts)"
  sorry
lemma fresh_variables_local_local: "\<forall>v\<in>set (fresh_variables_local used ts). \<not> vu_global v"
  apply (induction ts arbitrary: used, auto)
  by (metis (poly_guards_query) set_ConsD variable_untyped.select_convs(3)) 
lemma fresh_variables_local_type: "map vu_type (fresh_variables_local used ts) = ts"
  apply (induction ts arbitrary: used, auto)
  by (metis list.simps(9) variable_untyped.select_convs(2))
  

lemma proctype_inhabited: "\<exists>p. well_typed_proc p \<and> proctype_of p = pT"
proof (rule,rule)
  def args == "fresh_variables_local [] (pt_argtypes pT) :: variable_untyped list"
  def ret == "Abs_expression_untyped \<lparr> eur_fun=(\<lambda>m. t_default (pt_returntype pT)), eur_type=pt_returntype pT, eur_vars=[] \<rparr> :: expression_untyped"
  def p == "(Proc Skip args ret)"
  show "well_typed_proc p" 
    unfolding p_def apply simp
    unfolding args_def using fresh_variables_local_distinct fresh_variables_local_local
    by (metis pred_list_def)
  show "proctype_of p = pT" 
    unfolding p_def args_def apply (simp add: fresh_variables_local_type)
    unfolding ret_def eu_type_def
    by (subst Abs_expression_untyped_inverse, auto)
qed



subsection {* Simply-typed lambda calculus over procedures *}

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
| wt_ProcRef: "i<length E \<Longrightarrow> E!i = T \<Longrightarrow> well_typed_proc'' E (ProcRef i) T"
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
lemma wt_ProcRef_iff: "(i<length E \<and> E!i = T) = well_typed_proc'' E (ProcRef i) T"
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


lemma well_typed_extend:
  shows "well_typed'' [] p \<Longrightarrow> well_typed'' E p"
    and "well_typed_proc'' [] q T \<Longrightarrow> well_typed_proc'' E q T"
proof -
  have "\<And>E F. well_typed'' F p \<Longrightarrow> well_typed'' (F@E) p"
   and "\<And>T E F. well_typed_proc'' F q T \<Longrightarrow> well_typed_proc'' (F@E) q T"
    proof (induction p and q)
    next case Assign thus ?case by (auto simp: wt_Assign_iff[symmetric])
    next case Sample thus ?case by (auto simp: wt_Sample_iff[symmetric])
    next case Seq thus ?case by (auto simp: wt_Seq_iff[symmetric])
    next case IfTE thus ?case by (auto simp: wt_IfTE_iff[symmetric])
    next case While thus ?case by (auto simp: wt_While_iff[symmetric])
    next case ProcRef thus ?case by (auto simp: wt_ProcRef_iff[symmetric] nth_append)
    next case Skip thus ?case by (auto simp: wt_Skip)
    next case (CallProc v p a) thus ?case by (auto simp: wt_CallProc_iff[symmetric])
    next case (ProcAbs p) thus ?case apply (auto simp: wt_ProcAbs_iff[symmetric])
      by (metis append_Cons)
    next case (Proc body args ret) thus ?case by (auto simp: wt_Proc_iff[symmetric])
    next case (ProcAppl p1 p2) thus ?case by (auto simp: wt_ProcAppl_iff[symmetric], metis)
  qed
  from assms this[where F="[]", simplified]
  show "well_typed'' [] p \<Longrightarrow> well_typed'' E p"
    and "well_typed_proc'' [] q T \<Longrightarrow> well_typed_proc'' E q T"
      by auto
qed


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

(* TODO remove? Try (seems to be handlede automatically by simp anyway) *)
lemma subst_eq [simp]: "subst_proc k u (ProcRef k) = u"
  by simp

(* TODO remove? Try (seems to be handlede automatically by simp anyway) *)
lemma subst_gt [simp]: "i < j ==> subst_proc i u (ProcRef j) = ProcRef (j - 1)"
  by (simp)

(* TODO remove? Try (seems to be handlede automatically by simp anyway) *)
lemma subst_lt [simp]: "j < i ==> subst_proc i u (ProcRef j) = ProcRef j"
  by (simp)

lemma lift_lift:
  shows "i < k + 1 \<Longrightarrow> lift_proc_in_prog (lift_proc_in_prog p i) (Suc k) = lift_proc_in_prog (lift_proc_in_prog p k) i"
  and   "i < k + 1 \<Longrightarrow> lift_proc (lift_proc t i) (Suc k) = lift_proc (lift_proc t k) i"
  by (induct p and t arbitrary: i k and i k) auto

lemma lift_subst [simp]:
  shows "j < Suc i \<Longrightarrow> lift_proc_in_prog (subst_proc_in_prog j s p) i = subst_proc_in_prog j (lift_proc s i) (lift_proc_in_prog p (Suc i))"
  and   "j < Suc i \<Longrightarrow> lift_proc (subst_proc j s t) i = subst_proc j (lift_proc s i) (lift_proc t (Suc i))"
by (induct p and t arbitrary: i j s and i j s)
    (simp_all add: diff_Suc lift_lift split: nat.split)

lemma lift_subst_lt:
  shows "i < j + 1 \<Longrightarrow> lift_proc_in_prog (subst_proc_in_prog j s p) i = subst_proc_in_prog (j+1) (lift_proc s i) (lift_proc_in_prog p i)"
  and   "i < j + 1 \<Longrightarrow> lift_proc (subst_proc j s t) i = subst_proc (j+1) (lift_proc s i) (lift_proc t i)"
  apply (induct p and t arbitrary: i j s and i j s)
  by (simp_all add: lift_lift)

lemma subst_lift [simp]:
  shows "subst_proc_in_prog k s (lift_proc_in_prog p k) = p"
  and   "subst_proc k s (lift_proc t k) = t"
  by (induct p and t arbitrary: k s and k s) simp_all



lemma subst_subst:
  shows "i < Suc j \<Longrightarrow> subst_proc_in_prog i (subst_proc j v u) (subst_proc_in_prog (Suc j) (lift_proc v i) p) = subst_proc_in_prog j v (subst_proc_in_prog i u p)"
  and   "i < Suc j \<Longrightarrow> subst_proc i (subst_proc j v u) (subst_proc (Suc j) (lift_proc v i) q) = subst_proc j v (subst_proc i u q)"
  by (induct p and q arbitrary: i j u v and i j u v)
    (simp_all add: diff_Suc lift_lift [symmetric] lift_subst_lt
      split: nat.split)

(*
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
*)

inductive beta_reduce_prog :: "program_rep \<Rightarrow> program_rep \<Rightarrow> bool"
      and beta_reduce_proc :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> bool" where
  "beta_reduce_prog s t \<Longrightarrow> beta_reduce_prog (Seq s u) (Seq t u)"
| "beta_reduce_prog s t \<Longrightarrow> beta_reduce_prog (Seq u s) (Seq u t)"
| "beta_reduce_prog s t \<Longrightarrow> beta_reduce_prog (IfTE c s u) (IfTE c t u)"
| "beta_reduce_prog s t \<Longrightarrow> beta_reduce_prog (IfTE c u s) (IfTE c u t)"
| "beta_reduce_prog s t \<Longrightarrow> beta_reduce_prog (While c s) (While c t)"
| "beta_reduce_prog s t \<Longrightarrow> beta_reduce_prog (While c s) (While c t)"
| "beta_reduce_proc s t \<Longrightarrow> beta_reduce_prog (CallProc x s a) (CallProc x t a)"
| "beta_reduce_prog s t \<Longrightarrow> beta_reduce_proc (Proc s x y) (Proc t x y)"
| "beta_reduce_proc (ProcAppl (ProcAbs s) t) (subst_proc 0 t s)"
| "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcAppl s u) (ProcAppl t u)"
| "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcAppl u s) (ProcAppl u t)"
| "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcAbs s) (ProcAbs t)"
  
inductive_cases
    brc_Skip: "beta_reduce_prog Skip u"
and brc_Assign: "beta_reduce_prog (Assign x e) u"
and brc_Sample: "beta_reduce_prog (Sample x e) u"
and brc_Seq: "beta_reduce_prog (Seq p q) u"
and brc_IfTE: "beta_reduce_prog (IfTE c p q) u"
and brc_While: "beta_reduce_prog (While c p) u"
and brc_CallProc: "beta_reduce_prog (CallProc x p a) u"
and brc_Proc: "beta_reduce_proc (Proc body ret args) u"
and brc_ProcAppl: "beta_reduce_proc (ProcApply p1 p2) u"
and brc_ProcAbs: "beta_reduce_proc (ProcAbs p) u"


locale beta_reduce_proofs begin

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

abbreviation "ProcT == Fun (Atom 0) (Atom 0)"

fun typ_conv :: "procedure_type_open \<Rightarrow> LambdaType.type" where
  "typ_conv (ProcSimple _) = ProcT"
| "typ_conv (ProcFun T U) = Fun (typ_conv T) (typ_conv U)"

lemma typ_pres:
  shows "well_typed'' E pg \<Longrightarrow> (\<lambda>i. typ_conv (E!i)) \<turnstile> prog_to_dB pg : ProcT"
  and   "well_typed_proc'' E p T \<Longrightarrow>(\<lambda>i. typ_conv (E!i)) \<turnstile> proc_to_dB p : typ_conv T"
proof (induction E pg and E p T rule:well_typed''_well_typed_proc''.inducts)
case (wt_ProcAbs T E p U) show ?case apply auto 
  apply (rule rev_iffD1[OF wt_ProcAbs.IH])
  apply (tactic "cong_tac 1")+
  by (auto simp: shift_def)
qed auto

(*
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
*)


lemma accp_map: 
  assumes "Wellfounded.accp R (f z)"
  shows "Wellfounded.accp (\<lambda>x y. R (f x) (f y)) z"
proof -
  {fix x have "Wellfounded.accp R x \<Longrightarrow> x=f z 
     \<Longrightarrow> Wellfounded.accp (\<lambda>x y. R (f x) (f y)) z"
     apply (induction  arbitrary: z rule:Wellfounded.accp.induct)
     by (metis not_accp_down)}
  with assms show ?thesis by auto
qed

lemma termip_map: 
  assumes "termip R (f z)"
  shows "termip (\<lambda>x y. R (f x) (f y)) z"
proof -
  {fix x have "termip R x \<Longrightarrow> x=f z 
     \<Longrightarrow> termip (\<lambda>x y. R (f x) (f y)) z"
     apply (induction  arbitrary: z rule:Wellfounded.accp.induct, auto)
     by (metis (no_types, lifting) conversep_iff not_accp_down)}
  with assms show ?thesis by auto
qed

lemma well_typed_beta_reduce:
  assumes "well_typed_proc'' E p T"
  shows "termip beta_reduce_proc p"
proof -
  def beta1 == "\<lambda>p q. (prog_to_dB p) \<rightarrow>\<^sub>\<beta> (prog_to_dB q)"
  def beta2 == "\<lambda>p q. (proc_to_dB p) \<rightarrow>\<^sub>\<beta> (proc_to_dB q)"

  {fix p1 p2 q1 q2 
   have "beta_reduce_prog p1 p2 \<Longrightarrow> beta1 p1 p2"
    and "beta_reduce_proc q1 q2 \<Longrightarrow> beta2 q1 q2"
    unfolding beta1_def beta2_def
    by (induction rule:beta_reduce_prog_beta_reduce_proc.inducts, auto)}
  note rel = this


  have leq: "beta_reduce_proc \<le> beta2" by (auto simp: rel)
  have termip_leq: "termip beta2 \<le> termip beta_reduce_proc"
    by (rule accp_subset, simp add: leq)
  have "(\<lambda>i. typ_conv (E!i)) \<turnstile> proc_to_dB p : typ_conv T" using assms by (rule typ_pres)
  hence "termip beta (proc_to_dB p)" by (rule StrongNorm.type_implies_termi)
  hence "termip beta2 p" unfolding beta2_def by (rule termip_map)
  with termip_leq show "termip beta_reduce_proc p" by auto
qed


inductive par_beta' :: "[program_rep, program_rep] => bool"  (infixl "\<rightarrow>>" 50)
and par_beta :: "[procedure_rep, procedure_rep] \<Rightarrow> bool" (infixl "\<Rightarrow>>" 50)
  where
  pb_Assign [simp, intro!]: "Assign x e \<rightarrow>> Assign x e"
| pb_Sample[simp, intro!]: "Sample x e \<rightarrow>> Sample x e"
| pb_Seq[simp, intro!]: "[| s \<rightarrow>> s'; t \<rightarrow>> t' |] ==> Seq s t \<rightarrow>> Seq s' t'"
| pb_Skip[simp, intro!]: "Skip \<rightarrow>> Skip"
| pb_IfTE[simp, intro!]: "[| s \<rightarrow>> s'; t \<rightarrow>> t' |] ==> IfTE c s t \<rightarrow>> IfTE c s' t'"
| pb_While[simp, intro!]: "[| s \<rightarrow>> s' |] ==> While c s \<rightarrow>> While c s'"
| pb_CallProc[simp, intro!]: "[| s \<Rightarrow>> s' |] ==> CallProc x s a \<rightarrow>> CallProc x s' a"
| pb_Proc[simp, intro!]: "[| s \<rightarrow>> s' |] ==> Proc s x y \<Rightarrow>> Proc s' x y"
| pb_ProcRef [simp, intro!]: "ProcRef n \<Rightarrow>> ProcRef n"
| pb_ProcAbs [simp, intro!]: "s \<Rightarrow>> t ==> ProcAbs s \<Rightarrow>> ProcAbs t"
| pb_ProcAppl [simp, intro!]: "[| s \<Rightarrow>> s'; t \<Rightarrow>> t' |] ==> ProcAppl s t \<Rightarrow>> ProcAppl s' t'"
| pb_beta [simp, intro!]: "[| s \<Rightarrow>> s'; t \<Rightarrow>> t' |] ==> ProcAppl (ProcAbs s) t \<Rightarrow>> subst_proc 0 t' s'"

inductive_cases par_beta_cases [elim!]:
  "Assign x e \<rightarrow>> u"
  "Sample x e \<rightarrow>> u"
  "Skip \<rightarrow>> u"
  "ProcRef n \<Rightarrow>> t"
  "ProcAbs s \<Rightarrow>> ProcAbs t"
  "ProcAppl (ProcAbs s) t \<Rightarrow>> u"
  "ProcAppl s t \<Rightarrow>> u"
  "ProcAbs s \<Rightarrow>> t"
  "Seq s t \<rightarrow>> u"
  "IfTE c s t \<rightarrow>> u"
  "While c s \<rightarrow>> u"
  "CallProc x s a \<rightarrow>> u"
  "Proc b r a \<Rightarrow>> u"

lemma par_beta_varL [simp]:
    "(ProcRef n \<Rightarrow>> t) = (t = ProcRef n)"
  by blast

lemma par_beta_refl [simp]: shows "p \<rightarrow>> p" and "t \<Rightarrow>> t"  (* par_beta_refl [intro!] causes search to blow up *)
  by (induct p and t) simp_all

lemma beta_subset_par_beta: 
shows "beta_reduce_prog <= par_beta'"
  and "beta_reduce_proc <= par_beta"
proof (rule_tac [2] predicate2I, rule predicate2I)
  fix x y x' y'
  show "beta_reduce_prog x' y' \<Longrightarrow> x' \<rightarrow>> y'"
   and "beta_reduce_proc x y \<Longrightarrow> x \<Rightarrow>> y"
  apply (induction rule:beta_reduce_prog_beta_reduce_proc.inducts)
     by (blast intro!: par_beta_refl)+
qed

inductive_cases beta_reduce_cases [elim!]:
  "beta_reduce_proc (ProcRef i) t"
  "beta_reduce_proc (ProcAbs r) s"
  "beta_reduce_proc (ProcAppl s t) u"
  "beta_reduce_prog (Seq s t) u"

lemma rtrancl_beta_Seq1 [intro!]:
  "beta_reduce_prog\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_prog\<^sup>*\<^sup>* (Seq s t) (Seq s' t)"
  apply (induct set: rtranclp)  apply auto
  by (metis beta_reduce_prog_beta_reduce_proc.intros(1) rtranclp.simps)

lemma rtrancl_beta_Seq2 [intro!]:
  "beta_reduce_prog\<^sup>*\<^sup>* t t' \<Longrightarrow> beta_reduce_prog\<^sup>*\<^sup>* (Seq s t) (Seq s t')"
  apply (induct set: rtranclp)  apply auto
  by (metis beta_reduce_prog_beta_reduce_proc.intros(2) rtranclp.simps)

lemma rtrancl_beta_IfTE1 [intro!]:
  "beta_reduce_prog\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_prog\<^sup>*\<^sup>* (IfTE c s t) (IfTE c s' t)"
  apply (induct set: rtranclp)  apply auto
  by (metis beta_reduce_prog_beta_reduce_proc.intros(3) rtranclp.simps)

lemma rtrancl_beta_IfTE2 [intro!]:
  "beta_reduce_prog\<^sup>*\<^sup>* t t' \<Longrightarrow> beta_reduce_prog\<^sup>*\<^sup>* (IfTE c s t) (IfTE c s t')"
  apply (induct set: rtranclp)  apply auto
  by (metis beta_reduce_prog_beta_reduce_proc.intros(4) rtranclp.simps)


lemma rtrancl_beta_While [intro!]:
  "beta_reduce_prog\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_prog\<^sup>*\<^sup>* (While c s) (While c s')"
  apply (induct set: rtranclp)  apply auto
  by (metis beta_reduce_prog_beta_reduce_proc.intros(5) rtranclp.simps)

lemma rtrancl_beta_CallProc [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_prog\<^sup>*\<^sup>* (CallProc x s a) (CallProc x s' a)"
apply (induct set: rtranclp)  apply auto
by (metis beta_reduce_prog_beta_reduce_proc.intros(7) rtranclp.simps)

lemma rtrancl_beta_Proc [intro!]:
  "beta_reduce_prog\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (Proc s x y) (Proc s' x y)"
apply (induct set: rtranclp)  apply auto
by (metis beta_reduce_prog_beta_reduce_proc.intros(8) rtranclp.simps)

lemma rtrancl_beta_ProcAbs [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcAbs s) (ProcAbs s')"
apply (induct set: rtranclp)  apply auto
by (metis beta_reduce_prog_beta_reduce_proc.intros(12) rtranclp.rtrancl_into_rtrancl)

lemma rtrancl_beta_ProcAppl1 [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcAppl s t) (ProcAppl s' t)"
  apply (induct set: rtranclp)  apply auto
by (metis beta_reduce_prog_beta_reduce_proc.intros(10) rtranclp.rtrancl_into_rtrancl)


lemma rtrancl_beta_ProcAppl2 [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* t t' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcAppl s t) (ProcAppl s t')"
  apply (induct set: rtranclp)  apply auto
by (metis beta_reduce_prog_beta_reduce_proc.intros(11) rtranclp.rtrancl_into_rtrancl)






(*lemma rtrancl_beta_Abs [intro!]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' ==> Abs s \<rightarrow>\<^sub>\<beta>\<^sup>* Abs s'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppL:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' ==> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<degree> t"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppR:
    "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' ==> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s \<degree> t'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_App [intro]:
    "[| s \<rightarrow>\<^sub>\<beta>\<^sup>* s'; t \<rightarrow>\<^sub>\<beta>\<^sup>* t' |] ==> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<degree> t'"
  by (blast intro!: rtrancl_beta_AppL rtrancl_beta_AppR intro: rtranclp_trans)
*)

lemma par_beta_subset_beta: shows "par_beta' <= beta_reduce_prog^**" and "par_beta <= beta_reduce_proc^**" 
proof (rule_tac [2] predicate2I, rule predicate2I)
  fix x y x' y'
  show "x' \<rightarrow>> y' \<Longrightarrow> beta_reduce_prog\<^sup>*\<^sup>* x' y'"
   and "x \<Rightarrow>> y \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* x y"
  proof (induction rule:par_beta'_par_beta.inducts)
  case pb_Assign thus ?case by auto
  next case pb_Sample thus ?case by auto
  next case (pb_Seq s s' t t') thus ?case
    apply (rule_tac rtranclp_trans[where y="Seq s' t"])
    apply (rule rtrancl_beta_Seq1, simp)
    by (rule rtrancl_beta_Seq2, simp)
  next case pb_Skip thus ?case by auto[]
  next case (pb_IfTE s s' t t' c) thus ?case
    apply (rule_tac y="IfTE c s' t" in rtranclp_trans)
    apply (rule rtrancl_beta_IfTE1, simp)
    by (rule rtrancl_beta_IfTE2, simp)
  next case (pb_While s s' c) thus ?case
    by (rule_tac rtrancl_beta_While, simp)
  next case (pb_CallProc s s') thus ?case
     by (rule_tac rtrancl_beta_CallProc, simp)
  next case (pb_Proc s s') thus ?case
     by (rule_tac rtrancl_beta_Proc, simp)
  next case (pb_ProcRef) thus ?case by auto
  next case (pb_ProcAbs s t) thus ?case
     by (rule_tac rtrancl_beta_ProcAbs, simp)
  next case (pb_ProcAppl s s' t t') thus ?case
    apply (rule_tac rtranclp_trans[where y="ProcAppl s' t"])
    apply (rule rtrancl_beta_ProcAppl1, simp)
    by (rule rtrancl_beta_ProcAppl2, simp)
  next case (pb_beta s s' t t') thus ?case
    apply (rule_tac rtranclp.rtrancl_into_rtrancl[where b="ProcAppl (ProcAbs s') t'"])
    apply (rule_tac rtranclp_trans[where y="ProcAppl (ProcAbs s) t'"])
    apply (rule rtrancl_beta_ProcAppl2, simp)
    apply (rule rtrancl_beta_ProcAppl1)
    apply (rule rtrancl_beta_ProcAbs, simp)
    using beta_reduce_prog_beta_reduce_proc.intros by auto
  qed
qed


lemma par_beta_lift [simp]:
  shows "t \<rightarrow>> t' \<Longrightarrow> lift_proc_in_prog t n \<rightarrow>> lift_proc_in_prog t' n"
    and "p \<Rightarrow>> p' \<Longrightarrow> lift_proc p n \<Rightarrow>> lift_proc p' n"
proof (induct t and p arbitrary: t' n and p' n) 
case (ProcAppl p1 p2) thus ?case by fastforce
(*  fix s s' t t'
  assume "\<And>p' n. ProcAbs s \<Rightarrow>> p' \<Longrightarrow> ProcAbs (lift_proc s (Suc n)) \<Rightarrow>> lift_proc p' n"
  also assume "s \<Rightarrow>> s'"
  hence "ProcAbs s \<Rightarrow>> ProcAbs s'" by auto
  ultimately have "ProcAbs (lift_proc s (Suc n)) \<Rightarrow>> lift_proc (ProcAbs s') n" by metis 
  hence "ProcAbs (lift_proc s (Suc n)) \<Rightarrow>> ProcAbs (lift_proc s' (Suc n))" by auto
  hence "lift_proc s (Suc n) \<Rightarrow>> lift_proc s' (Suc n)"
    by (metis open_proc_termination.par_beta_cases(5))
  assume "p2 \<Rightarrow>> t'" and "\<And>p' n. p2 \<Rightarrow>> p' \<Longrightarrow> lift_proc p2 n \<Rightarrow>> lift_proc p' n"
  hence "lift_proc p2 n \<Rightarrow>> lift_proc t' n" by auto
  have "ProcAppl (ProcAbs (lift_proc s (Suc n))) (lift_proc p2 n) \<Rightarrow>> subst_proc 0 (lift_proc t' n) (lift_proc s' (Suc n))"
    by (metis `lift_proc p2 n \<Rightarrow>> lift_proc t' n` `lift_proc s (Suc n) \<Rightarrow>> lift_proc s' (Suc n)` open_proc_termination.pb_beta)
  have "subst_proc 0 (lift_proc t' n) (lift_proc s' (Suc n)) = lift_proc (subst_proc 0 t' s') n"
    by (metis Procedures.lift_subst zero_less_Suc)
  show "ProcAppl (ProcAbs (lift_proc s (Suc n))) (lift_proc p2 n) \<Rightarrow>> lift_proc (subst_proc 0 t' s') n" *)
qed auto


lemma par_beta_subst:
  shows "s \<Rightarrow>> s' \<Longrightarrow> p \<rightarrow>> p' \<Longrightarrow> subst_proc_in_prog n s p \<rightarrow>> subst_proc_in_prog n s' p'"
    and "s \<Rightarrow>> s' \<Longrightarrow> t \<Rightarrow>> t' \<Longrightarrow> subst_proc n s t \<Rightarrow>> subst_proc n s' t'"
proof (induct p and t arbitrary: s s' p' n and s s' t' n)
case Assign thus ?case by auto
next case Sample thus ?case by auto
next case Skip thus ?case by auto
next case (Seq p q) thus ?case by auto
next case IfTE thus ?case by auto
next case While thus ?case by auto
next case CallProc thus ?case by auto
next case Proc thus ?case by auto
next case ProcRef thus ?case by auto
next case ProcAbs thus ?case by auto
next case (ProcAppl p q) thus ?case
   apply (auto simp: subst_subst [symmetric])
   by (fastforce intro!: par_beta_lift)
qed

subsection {* Confluence (directly) *}

(* If this lemma breaks, can use diamond_par_beta2 below instead. *)
lemma diamond_par_beta: "diamond par_beta"
proof -
  {fix x y x' y' 
  have "y' \<rightarrow>> x' \<Longrightarrow> \<forall>z'. y' \<rightarrow>> z' \<longrightarrow> (\<exists>u'. x' \<rightarrow>> u' \<and> z' \<rightarrow>> u')"
  and  "y \<Rightarrow>> x \<Longrightarrow> \<forall>z. y \<Rightarrow>> z \<longrightarrow> (\<exists>u. x \<Rightarrow>> u \<and> z \<Rightarrow>> u)"
    apply (induction y' x' and y x rule:par_beta'_par_beta.inducts)
    by (blast intro!: par_beta_subst)+}
  thus ?thesis 
    unfolding diamond_def commute_def square_def by auto
qed


subsection {* Complete developments *}

fun cd' :: "program_rep \<Rightarrow> program_rep"
and cd :: "procedure_rep \<Rightarrow> procedure_rep" where
  "cd' Skip = Skip"
| "cd' (Assign x e) = Assign x e"
| "cd' (Sample x e) = Sample x e"
| "cd' (Seq p1 p2) = Seq (cd' p1) (cd' p2)"
| "cd' (IfTE c p1 p2) = IfTE c (cd' p1) (cd' p2)"
| "cd' (While c p) = While c (cd' p)"
| "cd' (CallProc v p e) = CallProc v (cd p) e"
| "cd (Proc body args ret) = Proc (cd' body) args ret"
| "cd (ProcRef n) = ProcRef n"
| "cd (ProcAppl (Proc body ret args) t) = ProcAppl (Proc (cd' body) ret args) (cd t)"
| "cd (ProcAppl (ProcRef n) t) = ProcAppl (ProcRef n) (cd t)"
| "cd (ProcAppl (ProcAppl s1 s2) t) = ProcAppl (cd (ProcAppl s1 s2)) (cd t)"
| "cd (ProcAppl (ProcAbs u) t) = subst_proc 0 (cd t) (cd u)"
| "cd (ProcAbs s) = ProcAbs (cd s)"

lemma par_beta_cd:
  shows "s' \<rightarrow>> t' \<Longrightarrow> t' \<rightarrow>> cd' s'"
  and   "s \<Rightarrow>> t \<Longrightarrow> t \<Rightarrow>> cd s"
  apply (induct s' and s arbitrary: t' and t rule: cd'_cd.induct)
      apply auto
  by (fast intro!: par_beta_subst)

subsection {* Confluence (via complete developments) *}

(*lemma diamond_par_beta2: "diamond par_beta"
  apply (unfold diamond_def commute_def square_def)
  by (blast intro: par_beta_cd)*)


theorem beta_confluent: "confluent beta_reduce_proc"
  apply (rule diamond_to_confluence)
  close (rule diamond_par_beta)
  close (rule beta_subset_par_beta)
  by (rule par_beta_subset_beta)

(*
theorem newman:
  assumes lc: "\<And>a b c. 
    termip R a \<Longrightarrow>
    R a b \<Longrightarrow> R a c \<Longrightarrow>
    \<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d"
  assumes "termip R a"
      and "R\<^sup>*\<^sup>* a b"
      and "R\<^sup>*\<^sup>* a c"
  shows "\<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d"
proof -
  def S == "\<lambda>x y. R x y \<and> termip R x"
  have termipRS: "termip R \<le> termip S"
    by (rule accp_subset, auto simp: S_def)
  note le_fun_def[simp]

  have "wfP (S\<inverse>\<inverse>)"
    apply (rule accp_wfPI, auto)
    apply (case_tac "termip R x")
    using termipRS apply simp
    by (rule accpI, auto simp: S_def)

  have RS: "\<And>x y. termip R x \<Longrightarrow> R\<^sup>*\<^sup>* x y \<Longrightarrow> S\<^sup>*\<^sup>* x y"
  proof -
    fix x y assume "R\<^sup>*\<^sup>* x y"
    thus "termip R x \<Longrightarrow> S\<^sup>*\<^sup>* x y"
      apply (induction, auto)
      apply (rule rtranclp.rtrancl_into_rtrancl, auto simp: S_def)
      by (metis (poly_guards_query) accp_downwards rtranclp_converseI)
  qed

  have lcS: "\<And>a b c. S a b \<Longrightarrow> S a c \<Longrightarrow>
    \<exists>d. S\<^sup>*\<^sup>* b d \<and> S\<^sup>*\<^sup>* c d"
  proof - fix a b c
    assume "S a b" hence "R a b" and "termip R a" unfolding S_def by auto
    also assume "S a c" hence "R a c" unfolding S_def by auto
    ultimately obtain d where "R\<^sup>*\<^sup>* b d" and "R\<^sup>*\<^sup>* c d" using lc by blast
    from `termip R a` and `R a b` have "termip R b"
      by (metis accp_downward conversep_iff) 
    from `termip R a` and `R a c` have "termip R c"
      by (metis accp_downward conversep_iff) 
    from `termip R b` `R\<^sup>*\<^sup>* b d` have "S\<^sup>*\<^sup>* b d" by (rule RS)
    also from `termip R c` `R\<^sup>*\<^sup>* c d` have "S\<^sup>*\<^sup>* c d" by (rule RS)
    ultimately show "\<exists>d. S\<^sup>*\<^sup>* b d \<and> S\<^sup>*\<^sup>* c d" by auto
  qed

  obtain d where "S\<^sup>*\<^sup>* b d" and "S\<^sup>*\<^sup>* c d"
    apply (atomize_elim)
    apply (rule newman)
    apply (fact `wfP S\<inverse>\<inverse>`)
    apply (fact lcS)
    using `termip R a` `R\<^sup>*\<^sup>* a b` apply (rule RS)
    using `termip R a` `R\<^sup>*\<^sup>* a c` by (rule RS)
  

  show "\<exists>d. R\<^sup>*\<^sup>* b d \<and> R\<^sup>*\<^sup>* c d"
    apply (rule exI[of _ d], auto)
    apply (rule rtranclp_mono[where r=S, simplified, rule_format])
    apply (simp add: S_def, fact `S\<^sup>*\<^sup>* b d`)
    apply (rule rtranclp_mono[where r=S, simplified, rule_format])
    by (simp add: S_def, fact `S\<^sup>*\<^sup>* c d`)
qed
*)

end

definition "beta_reduced p == \<not>(\<exists>q. beta_reduce_proc p q)"
definition "beta_reduce p == THE q. beta_reduced q \<and> beta_reduce_proc\<^sup>*\<^sup>* p q"

lemma beta_unique:
  assumes "beta_reduced q" and "beta_reduce_proc\<^sup>*\<^sup>* p q"
      and "beta_reduced q'" and "beta_reduce_proc\<^sup>*\<^sup>* p q'"
  shows "q=q'"
proof -
  from assms obtain r where qr: "beta_reduce_proc\<^sup>*\<^sup>* q r" and q'r: "beta_reduce_proc\<^sup>*\<^sup>* q' r"
  using beta_reduce_proofs.beta_confluent unfolding diamond_def commute_def square_def by metis
  with assms show "q=q'"
    by (metis converse_rtranclpE beta_reduced_def)
qed

lemma beta_reduce_def2:
  assumes "termip beta_reduce_proc p"
  shows "beta_reduced (beta_reduce p)" and "beta_reduce_proc\<^sup>*\<^sup>* p (beta_reduce p)"
proof -
  have exq: "\<exists>q. beta_reduced q \<and> beta_reduce_proc\<^sup>*\<^sup>* p q"
    using assms apply (induction, simp)
    by (metis beta_reduced_def converse_rtranclp_into_rtranclp eq_imp_rtranclp)
  have "beta_reduced (beta_reduce p) \<and> beta_reduce_proc\<^sup>*\<^sup>* p (beta_reduce p)" (is "?P (beta_reduce p)")
    unfolding beta_reduce_def 
    by (rule theI'[of ?P], auto intro: exq beta_unique)
  thus "beta_reduced (beta_reduce p)" and "beta_reduce_proc\<^sup>*\<^sup>* p (beta_reduce p)"
    by auto
qed

lemmas well_typed_beta_reduce = beta_reduce_proofs.well_typed_beta_reduce

lemma beta_reduce_rewrite:
  assumes "termip beta_reduce_proc p"
  and "beta_reduce_proc\<^sup>*\<^sup>* p q"
  shows "beta_reduce p = beta_reduce q"
by (metis accp_downwards_aux assms(1) assms(2) beta_reduce_def2(1) beta_reduce_def2(2) beta_unique rtranclp_converseI rtranclp_trans)

definition "apply_procedure p arg = beta_reduce (ProcAppl p arg)"
definition "apply_procedures p args = fold apply_procedure p args"


(* Undoing syntax changes introduced by Lambda and LambdaType *)
declare [[syntax_ambiguity_warning = false]]
no_syntax "\<^const>Lambda.dB.App" :: "dB\<Rightarrow>dB\<Rightarrow>dB" (infixl "\<degree>" 200)
no_syntax "\<^const>Lambda.subst" :: "[dB, dB, nat] => dB"  ("_[_'/_]" [300, 0, 0] 300)
no_syntax "\<^const>Lambda.beta" :: "[dB, dB] => bool"  (infixl "\<rightarrow>\<^sub>\<beta>" 50)
no_syntax "\<^const>Lambda.beta_reds" :: "[dB, dB] => bool"  (infixl "->>" 50)
no_syntax "\<^const>Lambda.beta_reds" :: "[dB, dB] => bool"  (infixl "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50)
no_syntax "\<^const>LambdaType.shift" :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_<_:_>" [90, 0, 0] 91)
no_syntax "\<^const>LambdaType.shift" :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<langle>_:_\<rangle>" [90, 0, 0] 91)
no_syntax "\<^const>LambdaType.shift" :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<langle>_:_\<rangle>" [90, 0, 0] 91)
no_syntax "\<^const>LambdaType.type.Fun" :: "LambdaType.type \<Rightarrow> LambdaType.type \<Rightarrow> LambdaType.type"  (infixr "\<Rightarrow>" 200)
no_syntax "\<^const>LambdaType.typing" :: "(nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile> _ : _" [50, 50, 50] 50)
no_syntax "\<^const>LambdaType.typings_rel" :: "(nat \<Rightarrow> type) \<Rightarrow> dB list \<Rightarrow> type list \<Rightarrow> bool" ("_ ||- _ : _" [50, 50, 50] 50)
no_syntax "\<^const>LambdaType.typings_rel" :: "(nat \<Rightarrow> type) \<Rightarrow> dB list \<Rightarrow> type list \<Rightarrow> bool" ("_ \<tturnstile> _ : _" [50, 50, 50] 50)
no_syntax "\<^const>LambdaType.funs" :: "type list \<Rightarrow> type \<Rightarrow> type"  (infixr "=>>" 200)
no_syntax "\<^const>LambdaType.funs" :: "type list \<Rightarrow> type \<Rightarrow> type"  (infixr "\<Rrightarrow>" 200)

end


