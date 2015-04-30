theory Procedures
imports "~~/src/HOL/Proofs/Lambda/Commutation" TypedLambda Lang_Untyped 
begin

subsection {* Various facts and definitions *}

definition "freshvar vs = (SOME vn. \<forall>v\<in>set vs. vn \<noteq> vu_name v)"
lemma freshvar_def2: "\<forall>v\<in>set vs. (freshvar vs) \<noteq> vu_name v"
proof -
  have "\<exists>vn. vn \<notin> set (map vu_name vs)"
    apply (rule ex_new_if_finite)
    close (rule infinite_UNIV_listI)
    by auto
  hence "\<exists>vn. \<forall>v\<in>set vs. vn \<noteq> vu_name v"
    by (metis image_eqI set_map)
  thus ?thesis
    unfolding freshvar_def
    by (rule someI_ex)
qed

(*
lemma freshvar_global: "mk_variable_untyped (Variable (freshvar vs)) \<notin> set vs"
  sorry
lemma freshvar_local: "mk_variable_untyped (LVariable (freshvar vs)) \<notin> set vs"
  sorry
*)

fun fresh_variables_local :: "variable_untyped list \<Rightarrow> type list \<Rightarrow> variable_untyped list" where
  "fresh_variables_local used [] = []"
| "fresh_variables_local used (t#ts) =
    (let vn=freshvar used in 
     let v=\<lparr> vu_name=vn, vu_type=t, vu_global=False \<rparr> in
     v#fresh_variables_local (v#used) ts)"
lemma fresh_variables_local_distinct: "distinct (fresh_variables_local used ts)"
apply (induction ts, auto simp: Let_def)
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
    by metis
  show "proctype_of p = pT" 
    unfolding p_def args_def apply (simp add: fresh_variables_local_type)
    unfolding ret_def eu_type_def
    by (subst Abs_expression_untyped_inverse, auto)
qed



subsection {* Simply-typed lambda calculus over procedures *}

datatype procedure_type_open = 
   ProcTSimple procedure_type
 | ProcTFun procedure_type_open procedure_type_open
 | ProcTPair procedure_type_open procedure_type_open

inductive well_typed'' :: "procedure_type_open list \<Rightarrow> program_rep \<Rightarrow> bool"
and well_typed_proc'' :: "procedure_type_open list \<Rightarrow> procedure_rep \<Rightarrow> procedure_type_open \<Rightarrow> bool" where
  wt_Seq: "well_typed'' E p1 \<and> well_typed'' E p2 \<Longrightarrow> well_typed'' E (Seq p1 p2)"
| wt_Assign: "eu_type e = vu_type v \<Longrightarrow> well_typed'' E (Assign v e)"
| wt_Sample: "ed_type e = vu_type v \<Longrightarrow> well_typed'' E (Sample v e)"
| wt_Skip: "well_typed'' E Skip"
| wt_While: "eu_type e = bool_type \<Longrightarrow> well_typed'' E p \<Longrightarrow> well_typed'' E (While e p)"
| wt_IfTE: "eu_type e = bool_type \<Longrightarrow> well_typed'' E thn \<Longrightarrow>  well_typed'' E els \<Longrightarrow> well_typed'' E (IfTE e thn els)"
| wt_CallProc: "well_typed_proc'' E prc (ProcTSimple \<lparr> pt_argtypes=map eu_type args, pt_returntype=vu_type v \<rparr>) \<Longrightarrow>
   well_typed'' E (CallProc v prc args)"
| wt_Proc: "well_typed'' E body \<Longrightarrow>
   (\<forall>v\<in>set pargs. \<not> vu_global v) \<Longrightarrow>
   distinct pargs \<Longrightarrow>
   well_typed_proc'' E (Proc body pargs ret) (ProcTSimple \<lparr> pt_argtypes=map vu_type pargs, pt_returntype=eu_type ret\<rparr>)"
| wt_ProcRef: "i<length E \<Longrightarrow> E!i = T \<Longrightarrow> well_typed_proc'' E (ProcRef i) T"
| wt_ProcAppl: "well_typed_proc'' E p (ProcTFun T U) \<Longrightarrow>
  well_typed_proc'' E q T \<Longrightarrow>
  well_typed_proc'' E (ProcAppl p q) U"
| wt_ProcAbs: "well_typed_proc'' (T#E) p U \<Longrightarrow> well_typed_proc'' E (ProcAbs p) (ProcTFun T U)"
| wt_ProcPair: "well_typed_proc'' E p T \<Longrightarrow> well_typed_proc'' E q U \<Longrightarrow> well_typed_proc'' E (ProcPair p q) (ProcTPair T U)"
| wt_ProcUnpair: "well_typed_proc'' E p (ProcTPair T U) \<Longrightarrow> well_typed_proc'' E (ProcUnpair b p) (if b then T else U)"

lemma wt_Assign_iff[symmetric]: "(eu_type e = vu_type v) = well_typed'' E (Assign v e)"
  apply (rule iffI, simp add: wt_Assign)
  by (cases rule:well_typed''.cases, auto)
lemma wt_Seq_iff[symmetric]: "(well_typed'' E p1 \<and> well_typed'' E p2) = well_typed'' E (Seq p1 p2)"
  apply (rule iffI, simp add: wt_Seq)
  by (cases rule:well_typed''.cases, auto)
lemma wt_Sample_iff[symmetric]: "(ed_type e = vu_type v) = well_typed'' E (Sample v e)"
  apply (rule iffI, simp add: wt_Sample)
  by (cases rule:well_typed''.cases, auto)
lemma wt_While_iff[symmetric]: "(eu_type e = bool_type \<and> well_typed'' E p) = well_typed'' E (While e p)"
  apply (rule iffI, simp add: wt_While)
  by (cases rule:well_typed''.cases, auto)
lemma wt_IfTE_iff[symmetric]: "(eu_type e = bool_type \<and> well_typed'' E thn \<and>  well_typed'' E els) = well_typed'' E (IfTE e thn els)"
  apply (rule iffI, simp add: wt_IfTE)
  by (cases rule:well_typed''.cases, auto)
lemma wt_CallProc_iff[symmetric]: "
   well_typed_proc'' E prc (ProcTSimple \<lparr> pt_argtypes=map eu_type args, pt_returntype=vu_type v\<rparr>) =
   well_typed'' E (CallProc v prc args)"
  apply (rule iffI, auto simp: wt_CallProc)
  by (cases rule:well_typed''.cases, auto)
lemma wt_Proc_iff[symmetric]: "
  (T'=ProcTSimple \<lparr> pt_argtypes=map vu_type pargs, pt_returntype=eu_type ret\<rparr> \<and> 
   well_typed'' E body \<and>
   (\<forall>v\<in>set pargs. \<not> vu_global v) \<and>
   distinct pargs) =
   well_typed_proc'' E (Proc body pargs ret) T'"
  apply (rule iffI, simp add: wt_Proc)
  by (cases rule:well_typed_proc''.cases, auto)
lemma wt_ProcRef_iff[symmetric]: "(i<length E \<and> E!i = T) = well_typed_proc'' E (ProcRef i) T"
  apply (rule iffI, simp add: wt_ProcRef)
  by (cases rule:well_typed_proc''.cases, auto)
lemma wt_ProcAppl_iff[symmetric]: "(\<exists>T. well_typed_proc'' E p (ProcTFun T U) \<and>
  well_typed_proc'' E q T) =
  well_typed_proc'' E (ProcAppl p q) U"
  apply (rule iffI, auto simp: wt_ProcAppl)
  by (cases rule:well_typed_proc''.cases, auto)
lemma wt_ProcAbs_iff[symmetric]: "(\<exists>T U. TU = ProcTFun T U \<and> well_typed_proc'' (T#E) p U) = well_typed_proc'' E (ProcAbs p) TU"
  apply (rule iffI, auto simp: wt_ProcAbs)
  by (cases rule:well_typed_proc''.cases, auto)
lemma wt_ProcPair_iff[symmetric]: "(\<exists>T U. TU = ProcTPair T U \<and> well_typed_proc'' E p T \<and> well_typed_proc'' E q U) = well_typed_proc'' E (ProcPair p q) TU"
  apply (rule iffI, auto simp: wt_ProcPair)
  by (cases rule:well_typed_proc''.cases, auto)
lemma wt_ProcUnpair_iff[symmetric]: "(\<exists>T U. TU = (if b then T else U) \<and> well_typed_proc'' E p (ProcTPair T U))
  = well_typed_proc'' E (ProcUnpair b p) TU"
  apply (rule iffI, auto simp: wt_ProcUnpair)
  apply (cases rule:well_typed_proc''.cases, auto)
  by (cases b, auto)

lemma well_typed_extend:
  shows "well_typed'' [] p \<Longrightarrow> well_typed'' E p"
    and "well_typed_proc'' [] q T \<Longrightarrow> well_typed_proc'' E q T"
proof -
  have "\<And>E F. well_typed'' F p \<Longrightarrow> well_typed'' (F@E) p"
   and "\<And>T E F. well_typed_proc'' F q T \<Longrightarrow> well_typed_proc'' (F@E) q T"
    proof (induction p and q)
    next case Assign thus ?case by (auto simp: wt_Assign_iff)
    next case Sample thus ?case by (auto simp: wt_Sample_iff)
    next case Seq thus ?case by (auto simp: wt_Seq_iff)
    next case IfTE thus ?case by (auto simp: wt_IfTE_iff)
    next case While thus ?case by (auto simp: wt_While_iff)
    next case ProcRef thus ?case by (auto simp: wt_ProcRef_iff nth_append)
    next case Skip thus ?case by (auto simp: wt_Skip)
    next case (CallProc v p a) thus ?case by (auto simp: wt_CallProc_iff)
    next case (ProcAbs p) thus ?case apply (auto simp: wt_ProcAbs_iff)
      by (metis append_Cons)
    next case (Proc body args ret) thus ?case by (auto simp: wt_Proc_iff)
    next case (ProcAppl p1 p2) thus ?case by (auto simp: wt_ProcAppl_iff, metis)
    next case (ProcPair p q T E F) thus ?case by (auto simp: wt_ProcPair_iff)
    next case (ProcUnpair b p T E F) thus ?case apply (auto simp: wt_ProcUnpair_iff)
      by (cases b, auto)
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
| "lift_proc (ProcPair s t) k = ProcPair (lift_proc s k) (lift_proc t k)"
| "lift_proc (ProcUnpair b s) k = ProcUnpair b (lift_proc s k)"
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
| subst_proc_ProcPair: "subst_proc k s (ProcPair t u) = ProcPair (subst_proc k s t) (subst_proc k s u)"
| subst_proc_ProcUnpair: "subst_proc k s (ProcUnpair b t) = ProcUnpair b (subst_proc k s t)"
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
  br_Seq1: "beta_reduce_prog s t \<Longrightarrow> beta_reduce_prog (Seq s u) (Seq t u)"
| br_Seq2: "beta_reduce_prog s t \<Longrightarrow> beta_reduce_prog (Seq u s) (Seq u t)"
| br_IfTE1: "beta_reduce_prog s t \<Longrightarrow> beta_reduce_prog (IfTE c s u) (IfTE c t u)"
| br_IfTE2: "beta_reduce_prog s t \<Longrightarrow> beta_reduce_prog (IfTE c u s) (IfTE c u t)"
| br_While: "beta_reduce_prog s t \<Longrightarrow> beta_reduce_prog (While c s) (While c t)"
(*| br_Whilx: "beta_reduce_prog s t \<Longrightarrow> beta_reduce_prog (While c s) (While c t)"*)
| br_CallProc: "beta_reduce_proc s t \<Longrightarrow> beta_reduce_prog (CallProc x s a) (CallProc x t a)"
| br_Proc: "beta_reduce_prog s t \<Longrightarrow> beta_reduce_proc (Proc s x y) (Proc t x y)"
| br_beta: "beta_reduce_proc (ProcAppl (ProcAbs s) t) (subst_proc 0 t s)"
| br_ProcAppl1: "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcAppl s u) (ProcAppl t u)"
| br_ProcAppl2: "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcAppl u s) (ProcAppl u t)"
| br_ProcAbs: "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcAbs s) (ProcAbs t)"
| br_ProcPair1: "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcPair s u) (ProcPair t u)"
| br_ProcPair2: "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcPair u s) (ProcPair u t)"
| br_ProcUnpair: "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcUnpair b s) (ProcUnpair b t)"
| br_ProcUnpairPair: "beta_reduce_proc (ProcUnpair b (ProcPair s t)) (if b then s else t)"
  
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
and brc_ProcPair: "beta_reduce_proc (ProcPair p1 p2) u"
and brc_ProcUnpair: "beta_reduce_proc (ProcUnpair b p) u"



locale beta_reduce_proofs begin



abbreviation "Proc0 == Abs(Var 0)"
abbreviation "Proc1 == Abs(Var 0)"
abbreviation "Proc2 == Abs(Abs(Var 0))"

(*

T \<longrightarrow> (T\<Rightarrow>unit) \<Rightarrow> unit

Abs A : T\<Rightarrow>U \<longrightarrow> %p. p (%t. A') : ((T\<Rightarrow>U) \<Rightarrow> unit) \<Rightarrow> unit
A' : T |- (U\<Rightarrow>unit) \<Rightarrow> unit
%t. A': T \<Rightarrow> (U\<Rightarrow>unit) \<Rightarrow> unit
p (%t A') : 

inl a :: (%x y. x a)
inr b :: (%x y. y b)
T+U == 

pair a b = (\<lambda>x. x a b) ::
T*U == (T \<Rightarrow> U \<Rightarrow> T+U) \<Rightarrow> T+U

fst p = p (%x y. x) :: T*U \<Rightarrow> T+U


*)


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
| "proc_to_dB (ProcPair p q) = MkPair (proc_to_dB p) (proc_to_dB q)"
| "proc_to_dB (ProcUnpair b p) = Unpair b (proc_to_dB p)"

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

fun typ_conv :: "procedure_type_open \<Rightarrow> TypedLambda.type" where
  "typ_conv (ProcTSimple _) = ProcT"
| "typ_conv (ProcTFun T U) = Fun (typ_conv T) (typ_conv U)"
| "typ_conv (ProcTPair T U) = Prod (typ_conv T) (typ_conv U)"

lemma typ_pres:
  shows "well_typed'' E pg \<Longrightarrow> (\<lambda>i. typ_conv (E!i)) \<turnstile> prog_to_dB pg : ProcT"
  and   "well_typed_proc'' E p T \<Longrightarrow>(\<lambda>i. typ_conv (E!i)) \<turnstile> proc_to_dB p : typ_conv T"
proof (induction E pg and E p T rule:well_typed''_well_typed_proc''.inducts)
case (wt_ProcAbs T E p U) show ?case apply auto 
  apply (rule rev_iffD1[OF wt_ProcAbs.IH])
  apply (tactic "cong_tac 1")+
  by (auto simp: shift_def)
qed auto




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
  shows "well_typed'' E p' \<Longrightarrow> termip beta_reduce_prog p'"
    and "well_typed_proc'' E p T \<Longrightarrow> termip beta_reduce_proc p"
proof -
  def beta1 == "\<lambda>p q. (prog_to_dB p) \<rightarrow>\<^sub>\<beta> (prog_to_dB q)"
  def beta2 == "\<lambda>p q. (proc_to_dB p) \<rightarrow>\<^sub>\<beta> (proc_to_dB q)"

  {fix p1 p2 q1 q2 
   have "beta_reduce_prog p1 p2 \<Longrightarrow> beta1 p1 p2"
    and "beta_reduce_proc q1 q2 \<Longrightarrow> beta2 q1 q2"
    unfolding beta1_def beta2_def
    by (induction rule:beta_reduce_prog_beta_reduce_proc.inducts, auto)}
  note rel = this

  show "well_typed_proc'' E p T \<Longrightarrow> termip beta_reduce_proc p"
  proof -
    assume wt: "well_typed_proc'' E p T"
    have leq: "beta_reduce_proc \<le> beta2" by (auto simp: rel)
    have termip_leq: "termip beta2 \<le> termip beta_reduce_proc"
      by (rule accp_subset, simp add: leq)
    have "(\<lambda>i. typ_conv (E!i)) \<turnstile> proc_to_dB p : typ_conv T" using wt by (rule typ_pres)
    hence "termip beta (proc_to_dB p)" by (rule type_implies_termi)
    hence "termip beta2 p" unfolding beta2_def by (rule termip_map)
    with termip_leq show ?thesis by auto
  qed

  show "well_typed'' E p' \<Longrightarrow> termip beta_reduce_prog p'"
  proof -
    assume wt: "well_typed'' E p'"
    have leq: "beta_reduce_prog \<le> beta1" by (auto simp: rel)
    have termip_leq: "termip beta1 \<le> termip beta_reduce_prog"
      by (rule accp_subset, simp add: leq)
    have "(\<lambda>i. typ_conv (E!i)) \<turnstile> prog_to_dB p' : ProcT" using wt by (rule typ_pres)
    hence "termip beta (prog_to_dB p')" by (rule type_implies_termi)
    hence "termip beta1 p'" unfolding beta1_def by (rule termip_map)
    with termip_leq show ?thesis by auto
  qed
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
| pb_ProcPair [simp, intro!]: "[| s \<Rightarrow>> s'; t \<Rightarrow>> t' |] ==> ProcPair s t \<Rightarrow>> ProcPair s' t'"
| pb_ProcUnpair [simp, intro!]: "s \<Rightarrow>> t ==> ProcUnpair b s \<Rightarrow>> ProcUnpair b t"
| pb_ProcUnpair1 [simp, intro!]: "s \<Rightarrow>> s' ==> ProcUnpair True (ProcPair s t) \<Rightarrow>> s'"
| pb_ProcUnpair2 [simp, intro!]: "t \<Rightarrow>> t' ==> ProcUnpair False (ProcPair s t) \<Rightarrow>> t'"
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
  "ProcPair p1 p2 \<Rightarrow>> u"
  "ProcUnpair b p \<Rightarrow>> u"

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
     apply (blast intro!: par_beta_refl)+
proof -
  fix b :: bool and s :: procedure_rep and t :: procedure_rep
  obtain sp\<^sub>2 :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> bool" and sk\<^sub>1\<^sub>2 :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> procedure_rep" and sk\<^sub>1\<^sub>1 :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> procedure_rep" and sk\<^sub>1\<^sub>0 :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> procedure_rep" and sk\<^sub>9 :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> procedure_rep" and sk\<^sub>8 :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> procedure_rep" and sp\<^sub>5 :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> bool" and sp\<^sub>1 :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> bool" and sp\<^sub>0 :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> bool" and sp\<^sub>4 :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> bool" and sk\<^sub>7 :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> nat" and sp\<^sub>3 :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> bool" and sp\<^sub>6 :: "procedure_rep \<Rightarrow> procedure_rep \<Rightarrow> bool" where "sp\<^sub>6 (if b then s else t) (ProcUnpair b (ProcPair s t))" by simp
  thus "ProcUnpair b (ProcPair s t) \<Rightarrow>> (if b then s else t)"
    by (metis (full_types) beta_reduce_proofs.par_beta_refl(2) beta_reduce_proofs.pb_ProcUnpair1 beta_reduce_proofs.pb_ProcUnpair2)
  qed
qed

inductive_cases beta_reduce_cases [elim!]:
  "beta_reduce_proc (ProcRef i) t"
  "beta_reduce_proc (ProcAbs r) s"
  "beta_reduce_proc (ProcAppl s t) u"
  "beta_reduce_proc (ProcPair s t) s"
  "beta_reduce_proc (ProcUnpair b t) u"
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
by (metis beta_reduce_prog_beta_reduce_proc.intros(6) rtranclp.simps)

lemma rtrancl_beta_Proc [intro!]:
  "beta_reduce_prog\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (Proc s x y) (Proc s' x y)"
apply (induct set: rtranclp)  apply auto
by (metis beta_reduce_prog_beta_reduce_proc.intros(7) rtranclp.simps)

lemma rtrancl_beta_ProcAbs [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcAbs s) (ProcAbs s')"
apply (induct set: rtranclp)  apply auto
by (metis beta_reduce_prog_beta_reduce_proc.intros(11) rtranclp.rtrancl_into_rtrancl)

lemma rtrancl_beta_ProcAppl1 [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcAppl s t) (ProcAppl s' t)"
  apply (induct set: rtranclp)  apply auto
by (metis beta_reduce_prog_beta_reduce_proc.intros(9) rtranclp.rtrancl_into_rtrancl)


lemma rtrancl_beta_ProcAppl2 [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* t t' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcAppl s t) (ProcAppl s t')"
  apply (induct set: rtranclp)  apply auto
by (metis beta_reduce_prog_beta_reduce_proc.intros(10) rtranclp.rtrancl_into_rtrancl)

lemma rtrancl_beta_ProcPair1 [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcPair s t) (ProcPair s' t)"
  apply (induct set: rtranclp)  apply auto
  by (metis beta_reduce_prog_beta_reduce_proc.intros(12) rtranclp.rtrancl_into_rtrancl)


lemma rtrancl_beta_ProcPair2 [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* t t' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcPair s t) (ProcPair s t')"
  apply (induct set: rtranclp)  apply auto
  by (metis beta_reduce_prog_beta_reduce_proc.intros(13) rtranclp.rtrancl_into_rtrancl)

lemma rtrancl_beta_ProcUnpair [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcUnpair b s) (ProcUnpair b s')"
  apply (induct set: rtranclp)  apply auto
  by (metis beta_reduce_prog_beta_reduce_proc.intros(14) rtranclp.rtrancl_into_rtrancl)






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
  next case (pb_ProcPair s s' t t') thus ?case
    apply (rule_tac rtranclp_trans[where y="ProcPair s' t"])
    apply (rule rtrancl_beta_ProcPair1, simp)
    by (rule rtrancl_beta_ProcPair2, simp)
  next case (pb_ProcUnpair s t b) thus ?case
     by (rule_tac rtrancl_beta_ProcUnpair, simp)
  next case (pb_ProcUnpair1 s s' t) thus ?case
    apply (rule_tac Transitive_Closure.converse_rtranclp_into_rtranclp[where b=s], auto)
    using beta_reduce_prog_beta_reduce_proc.intros by presburger
  next case (pb_ProcUnpair2 t t' s) thus ?case
    apply (rule_tac Transitive_Closure.converse_rtranclp_into_rtranclp[where b=t], auto)
    using beta_reduce_prog_beta_reduce_proc.intros by (metis (full_types))
  qed
qed


lemma par_beta_lift [simp]:
  shows "t \<rightarrow>> t' \<Longrightarrow> lift_proc_in_prog t n \<rightarrow>> lift_proc_in_prog t' n"
    and "p \<Rightarrow>> p' \<Longrightarrow> lift_proc p n \<Rightarrow>> lift_proc p' n"
proof (induct t and p arbitrary: t' n and p' n) 
case (ProcAppl p1 p2) thus ?case by fastforce
next case (ProcPair p1 p2) thus ?case by fastforce
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
next case (ProcUnpair b p)
(*     p \<Rightarrow>> ?p' \<Longrightarrow> lift_proc p ?n \<Rightarrow>> lift_proc ?p' ?n
     *) 
  from ProcUnpair.prems show ?case
  proof (erule_tac par_beta_cases)
    fix t assume p':"p' = ProcUnpair b t" and "p \<Rightarrow>> t" 
    with ProcUnpair.hyps show "lift_proc (ProcUnpair b p) n \<Rightarrow>> lift_proc p' n" by auto
  next
    fix s t assume b:"b" assume sp':"s \<Rightarrow>> p'" assume p:"p = ProcPair s t"
    have "p \<Rightarrow>> ProcPair p' t"  unfolding p
      using sp' by auto
    with ProcUnpair.hyps
    have "lift_proc p n \<Rightarrow>> lift_proc (ProcPair p' t) n" by metis
    also have "lift_proc p n = ProcPair (lift_proc s n) (lift_proc t n)"
      by (metis lift_proc.simps(4) p)
    finally have "lift_proc s n \<Rightarrow>> lift_proc p' n" by auto
    thus "lift_proc (ProcUnpair b p) n \<Rightarrow>> lift_proc p' n" 
      unfolding p using b by auto
  next
    fix s t assume b:"\<not>b" assume sp':"t \<Rightarrow>> p'" assume p:"p = ProcPair s t"
    have "p \<Rightarrow>> ProcPair s p'"  unfolding p
      using sp' by auto
    with ProcUnpair.hyps
    have "lift_proc p n \<Rightarrow>> lift_proc (ProcPair s p') n" by metis
    also have "lift_proc p n = ProcPair (lift_proc s n) (lift_proc t n)"
      by (metis lift_proc.simps(4) p)
    finally have "lift_proc t n \<Rightarrow>> lift_proc p' n" by auto
    thus "lift_proc (ProcUnpair b p) n \<Rightarrow>> lift_proc p' n" 
      unfolding p using b by auto
  qed
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
next case (ProcUnpair b t) 
  from ProcUnpair.prems show ?case
  proof (erule_tac par_beta_cases)
    fix t0 assume "s \<Rightarrow>> s'" and "t' = ProcUnpair b t0" and "t \<Rightarrow>> t0"
    thus "subst_proc n s (ProcUnpair b t) \<Rightarrow>> subst_proc n s' t'"
      by (metis (poly_guards_query) ProcUnpair.hyps Procedures.subst_proc_ProcUnpair beta_reduce_proofs.pb_ProcUnpair)
  next
    fix s0 t0 assume ss': "s \<Rightarrow>> s'" assume s0t': "s0 \<Rightarrow>> t'"
    assume b:"b" assume t:"t = ProcPair s0 t0"
    from t s0t' have "t \<Rightarrow>> ProcPair t' t0" by auto
    with ss' have "subst_proc n s (ProcPair s0 t0) \<Rightarrow>> subst_proc n s' (ProcPair t' t0)" 
      unfolding t[symmetric] by (rule_tac ProcUnpair.hyps, auto)
    hence "subst_proc n s s0 \<Rightarrow>> subst_proc n s' t'" by auto
    thus "subst_proc n s (ProcUnpair b t) \<Rightarrow>> subst_proc n s' t'"
      by (auto simp: t b)
  next
    fix s0 t0 assume ss': "s \<Rightarrow>> s'" assume s0t': "t0 \<Rightarrow>> t'"
    assume b:"\<not>b" assume t:"t = ProcPair s0 t0"
    from t s0t' have "t \<Rightarrow>> ProcPair s0 t'" by auto
    with ss' have "subst_proc n s (ProcPair s0 t0) \<Rightarrow>> subst_proc n s' (ProcPair s0 t')" 
      unfolding t[symmetric] by (rule_tac ProcUnpair.hyps, auto)
    hence "subst_proc n s t0 \<Rightarrow>> subst_proc n s' t'" by auto
    thus "subst_proc n s (ProcUnpair b t) \<Rightarrow>> subst_proc n s' t'"
      by (auto simp: t b)
  qed
next case (ProcPair p q) thus ?case
   by (auto simp: subst_subst [symmetric])
qed

subsection {* Confluence (directly) *}

(* If this lemma breaks, can use diamond_par_beta2 below instead. *)
lemma diamond_par_beta: "diamond par_beta"
proof -
  {fix x y x' y' 
  have "y' \<rightarrow>> x' \<Longrightarrow> \<forall>z'. y' \<rightarrow>> z' \<longrightarrow> (\<exists>u'. x' \<rightarrow>> u' \<and> z' \<rightarrow>> u')"
  and  "y \<Rightarrow>> x \<Longrightarrow> \<forall>z. y \<Rightarrow>> z \<longrightarrow> (\<exists>u. x \<Rightarrow>> u \<and> z \<Rightarrow>> u)"
    proof (induction y' x' and y x rule:par_beta'_par_beta.inducts)
    case pb_Assign thus ?case by (blast intro!: par_beta_subst)
    next case pb_Sample thus ?case by (blast intro!: par_beta_subst)
    next case pb_Seq thus ?case by (blast intro!: par_beta_subst)
    next case pb_Skip thus ?case by (blast intro!: par_beta_subst)
    next case pb_IfTE thus ?case by (blast intro!: par_beta_subst)
    next case pb_While thus ?case by (blast intro!: par_beta_subst)
    next case pb_CallProc thus ?case by (blast intro!: par_beta_subst)
    next case pb_Proc thus ?case by (blast intro!: par_beta_subst)
    next case pb_ProcRef thus ?case by (blast intro!: par_beta_subst)
    next case pb_ProcAbs thus ?case by (blast intro!: par_beta_subst)
    next case pb_ProcAppl thus ?case by (blast intro!: par_beta_subst)
    next case pb_ProcPair thus ?case by (blast intro!: par_beta_subst)
    next case pb_beta thus ?case by (blast intro!: par_beta_subst)
    next case pb_ProcUnpair1 thus ?case by (blast intro!: par_beta_subst)
    next case pb_ProcUnpair2 thus ?case by (blast intro!: par_beta_subst)
    next case (pb_ProcUnpair s t b) show ?case 
      proof auto
        fix ta assume "s \<Rightarrow>> ta" 
        thus "\<exists>u. ProcUnpair b t \<Rightarrow>> u \<and> ProcUnpair b ta \<Rightarrow>> u"
          by (metis (full_types) beta_reduce_proofs.pb_ProcUnpair pb_ProcUnpair.IH)
      next
        fix z sa ta assume saz:"sa \<Rightarrow>> z" assume b assume s:"s = ProcPair sa ta" 
        thm pb_ProcUnpair.IH
        obtain u where tu:"t \<Rightarrow>> u" and ztau:"ProcPair z ta \<Rightarrow>> u"
          by (metis saz beta_reduce_proofs.par_beta_refl(2) beta_reduce_proofs.pb_ProcPair pb_ProcUnpair.IH s)
        obtain u1 u2 where u:"u=ProcPair u1 u2" and zu1:"z\<Rightarrow>>u1"
          by (metis ztau beta_reduce_proofs.par_beta_cases(14))
        obtain sa0 ta0 where t:"t = ProcPair sa0 ta0"
          by (metis s beta_reduce_proofs.par_beta_cases(14) pb_ProcUnpair.hyps)
        from tu have sa0u1: "sa0 \<Rightarrow>> u1" unfolding t u by (cases, auto)
        show "\<exists>u. ProcUnpair True t \<Rightarrow>> u \<and> z \<Rightarrow>> u"
          apply (rule exI[of _ u1])
          unfolding t using sa0u1 zu1 by auto
      next
        fix z sa ta assume taz:"ta \<Rightarrow>> z" assume "\<not>b" assume s:"s = ProcPair sa ta" 
        thm pb_ProcUnpair.IH
        obtain u where tu:"t \<Rightarrow>> u" and ztau:"ProcPair sa z \<Rightarrow>> u"
          by (metis taz beta_reduce_proofs.par_beta_refl(2) beta_reduce_proofs.pb_ProcPair pb_ProcUnpair.IH s)
        obtain u1 u2 where u:"u=ProcPair u1 u2" and zu2:"z\<Rightarrow>>u2"
          by (metis ztau beta_reduce_proofs.par_beta_cases(14))
        obtain sa0 ta0 where t:"t = ProcPair sa0 ta0"
          by (metis s beta_reduce_proofs.par_beta_cases(14) pb_ProcUnpair.hyps)
        from tu have ta0u2: "ta0 \<Rightarrow>> u2" unfolding t u by (cases, auto)
        show "\<exists>u. ProcUnpair False t \<Rightarrow>> u \<and> z \<Rightarrow>> u"
          apply (rule exI[of _ u2])
          unfolding t using ta0u2 zu2 by auto
      qed
    qed}
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
| "cd (ProcAppl (ProcAppl s1 s2) t) = ProcAppl (cd (ProcAppl s1 s2)) (cd t)"
| "cd (ProcAppl (ProcAbs u) t) = subst_proc 0 (cd t) (cd u)"
| "cd (ProcAppl t u) = ProcAppl (cd t) (cd u)"
| "cd (ProcAbs s) = ProcAbs (cd s)"
| "cd (ProcPair s t) = ProcPair (cd s) (cd t)"
| "cd (ProcUnpair b (ProcPair p1 p2)) = (if b then cd p1 else cd p2)"
| "cd (ProcUnpair b t) = ProcUnpair b (cd t)"

(*
lemma par_beta_cd:
  shows "s' \<rightarrow>> t' \<Longrightarrow> t' \<rightarrow>> cd' s'"
  and   "s \<Rightarrow>> t \<Longrightarrow> t \<Rightarrow>> cd s"
  apply (induct s' and s arbitrary: t' and t rule: cd'_cd.induct)
      apply auto
  close (fast intro!: par_beta_subst)
  close (fast intro!: par_beta_subst)
  by (fast intro!: par_beta_subst)
*)

subsection {* Confluence (via complete developments) *}

(*
lemma diamond_par_beta2: "diamond par_beta"
  apply (unfold diamond_def commute_def square_def)
  by (blast intro: par_beta_cd)
*)

theorem beta_confluent: "confluent beta_reduce_proc"
  apply (rule diamond_to_confluence)
  close (rule diamond_par_beta)
  close (rule beta_subset_par_beta)
  by (rule par_beta_subset_beta)

theorem beta_prog_confluent: "confluent beta_reduce_prog"
  SORRY "by reduction to beta_confluent?"

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

lemma well_typed_lift_proc: (* TODO: cleanup statement *)
  shows "well_typed'' (F@E) p' \<Longrightarrow> well_typed'' (F@U#E) (lift_proc_in_prog p' (length F))" (is "PROP ?thesis1")
    and "well_typed_proc'' (F@E) p T \<Longrightarrow> well_typed_proc'' (F@U#E) (lift_proc p (length F)) T" (is "PROP ?thesis2")
proof -
  def FE=="F@E"
  have "well_typed'' FE p' \<Longrightarrow> FE=F@E \<Longrightarrow> well_typed'' (F@U#E) (lift_proc_in_prog p' (length F))"
   and "well_typed_proc'' FE p T \<Longrightarrow> FE=F@E \<Longrightarrow> well_typed_proc'' (F@U#E) (lift_proc p (length F)) T"
  proof (induction arbitrary: F E and F E rule:well_typed''_well_typed_proc''.inducts)
  case wt_Seq thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_Skip thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_Assign thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_Sample thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_While thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_IfTE thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_CallProc thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_Proc thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case (wt_ProcRef i FE T) 
    have c1: "i < length F \<Longrightarrow> ?case"
      apply simp
      apply (subst wt_ProcRef_iff, auto)
      using wt_ProcRef by (metis nth_append)
    have aux: "length F \<le> i \<Longrightarrow> (F@U#E) ! Suc i = (F@E) ! i"
      apply (induction F arbitrary: i, auto)
      by (metis Suc_le_D Suc_le_mono Suc_pred diff_Suc_1 zero_less_Suc)
    have c2: "i \<ge> length F \<Longrightarrow> ?case"
      apply simp apply (subst wt_ProcRef_iff, auto)
      using wt_ProcRef close auto
      using wt_ProcRef aux by auto
    from c1 c2 show ?case by simp
  next case wt_ProcAppl thus ?case by (metis (erased, hide_lams) lift_proc.simps(3) wt_ProcAppl_iff)
  next case (wt_ProcAbs T FUE p U) 
    show ?case 
      apply (simp, subst wt_ProcAbs_iff, auto)
      apply (rule wt_ProcAbs.IH[where E=E and F="T#F", simplified])
      using wt_ProcAbs by auto
  next case wt_ProcPair thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_ProcUnpair thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  qed
  with FE_def show "PROP ?thesis1" and "PROP ?thesis2" by auto
qed

lemma well_typed_subst_proc:
  assumes "well_typed_proc'' (F@E) q U"
  shows "well_typed'' (F@U#E) p' \<Longrightarrow> well_typed'' (F@E) (subst_proc_in_prog (length F) q p')" (is "PROP?thesis1")
    and "well_typed_proc'' (F@U#E) p T \<Longrightarrow> well_typed_proc'' (F@E) (subst_proc (length F) q p) T" (is "PROP?thesis2")
proof -
  def FUE=="F@U#E"
  have "well_typed'' FUE p' \<Longrightarrow> FUE=F@U#E \<Longrightarrow> well_typed_proc'' (F@E) q U \<Longrightarrow> well_typed'' (F@E) (subst_proc_in_prog (length F) q p')"
   and "well_typed_proc'' FUE p T \<Longrightarrow> FUE=F@U#E \<Longrightarrow> well_typed_proc'' (F@E) q U \<Longrightarrow> well_typed_proc'' (F@E) (subst_proc (length F) q p) T"
  proof (induction arbitrary: q F E and q F E rule:well_typed''_well_typed_proc''.inducts)
  case wt_Seq thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_Skip thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_Assign thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_Sample thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_While thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_IfTE thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_CallProc thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_Proc thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case (wt_ProcRef i FUE T)  
    have c1: "i < length F \<Longrightarrow> ?case"
      apply simp
      apply (subst wt_ProcRef_iff, auto)
      using wt_ProcRef by (metis nth_append)
    have c2: "i = length F \<Longrightarrow> ?case"
      apply simp using wt_ProcRef by (metis nth_append_length) 
    have aux: "i > length F \<Longrightarrow> (F@E) ! (i-Suc 0) = (F@U#E) ! i"
      apply (induction F arbitrary: i, auto)
      by (metis Suc_lessE diff_Suc_Suc minus_nat.diff_0)
    have c3: "i > length F \<Longrightarrow> ?case"
      apply simp apply (subst wt_ProcRef_iff, auto)
      using wt_ProcRef close auto
      using wt_ProcRef aux by auto
    from c1 c2 c3 show ?case by simp
  next case (wt_ProcAppl FUE p T U p2)
    show ?case
      apply (simp add: wt_ProcAppl_iff)
      apply (rule exI[of _ T], auto)
      using wt_ProcAppl close simp
      using wt_ProcAppl by metis
  next case (wt_ProcAbs T FUE p U) 
    show ?case 
      apply (simp, subst wt_ProcAbs_iff, auto)
      apply (rule wt_ProcAbs.IH[where E=E and F="T#F", simplified])
      using wt_ProcAbs close auto
      apply (rule well_typed_lift_proc[where F="[]", simplified])
      using wt_ProcAbs by auto
  next case wt_ProcPair thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  next case wt_ProcUnpair thus ?case by (auto simp:well_typed''_well_typed_proc''.intros)
  qed
  thus "PROP?thesis1" and "PROP?thesis2" using assms FUE_def by auto
qed

lemma subject_reduction:
  shows "beta_reduce_prog p' q' \<Longrightarrow> well_typed'' E p' \<Longrightarrow> well_typed'' E q'"
    and "beta_reduce_proc p q \<Longrightarrow> well_typed_proc'' E p T \<Longrightarrow> well_typed_proc'' E q T"
proof (induction arbitrary: E and E T rule:beta_reduce_prog_beta_reduce_proc.inducts)
case br_Seq1 thus ?case by (metis wt_Seq_iff)
next case br_Seq2 thus ?case by (metis wt_Seq_iff)
next case br_IfTE1 thus ?case by (metis wt_IfTE_iff)
next case br_IfTE2 thus ?case by (metis wt_IfTE_iff)
next case br_While thus ?case by (metis wt_While_iff)
next case br_ProcAbs thus ?case by (metis wt_ProcAbs_iff)
next case br_CallProc thus ?case by (metis wt_CallProc_iff)
next case br_Proc thus ?case by (metis wt_Proc_iff)
next case br_ProcAppl1 thus ?case by (metis wt_ProcAppl_iff)
next case br_ProcAppl2 thus ?case by (metis wt_ProcAppl_iff)
next case br_ProcPair1 thus ?case by (metis wt_ProcPair_iff)
next case br_ProcPair2 thus ?case by (metis wt_ProcPair_iff)
next case br_ProcUnpair thus ?case by (metis wt_ProcUnpair_iff)
next case br_ProcUnpairPair thus ?case
by (smt2 procedure_type_open.inject(3) program_rep_procedure_rep.simps(12) wt_ProcPair_iff wt_ProcUnpair_iff)
next case (br_beta s t) 
  then obtain U where abs_s: "well_typed_proc'' E (ProcAbs s) (ProcTFun U T)"
                  and t: "well_typed_proc'' E t U"
    by (metis wt_ProcAppl_iff) 
  from abs_s have s:"well_typed_proc'' (U#E) s T"
    by (metis procedure_type_open.inject(2) wt_ProcAbs_iff)
  show ?case 
    apply (rule well_typed_subst_proc(2)[where F="[]", simplified])
    by (fact t, fact s)
qed



definition "beta_reduced p == \<not>(\<exists>q. beta_reduce_proc p q)"
definition "beta_reduce p == 
  if (\<exists>q. beta_reduced q \<and> beta_reduce_proc\<^sup>*\<^sup>* p q)
  then (THE q. beta_reduced q \<and> beta_reduce_proc\<^sup>*\<^sup>* p q)
  else (Proc Skip [] undefined)"
definition "beta_reduced' p == \<not>(\<exists>q. beta_reduce_prog p q)"
definition "beta_reduce' p == 
  if (\<exists>q. beta_reduced' q \<and> beta_reduce_prog\<^sup>*\<^sup>* p q)
  then (THE q. beta_reduced' q \<and> beta_reduce_prog\<^sup>*\<^sup>* p q)
  else Skip"

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

lemma beta_unique':
  assumes "beta_reduced' q" and "beta_reduce_prog\<^sup>*\<^sup>* p q"
      and "beta_reduced' q'" and "beta_reduce_prog\<^sup>*\<^sup>* p q'"
  shows "q=q'"
proof -
  from assms obtain r where qr: "beta_reduce_prog\<^sup>*\<^sup>* q r" and q'r: "beta_reduce_prog\<^sup>*\<^sup>* q' r"
  using beta_reduce_proofs.beta_prog_confluent unfolding diamond_def commute_def square_def by metis
  with assms show "q=q'"
    by (metis converse_rtranclpE beta_reduced'_def)
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
    apply (subst exq, subst exq, simp)
    by (rule theI'[of ?P], auto intro: exq beta_unique)
  thus "beta_reduced (beta_reduce p)" and "beta_reduce_proc\<^sup>*\<^sup>* p (beta_reduce p)"
    by auto
qed

lemma beta_reduce'_def2:
  assumes "termip beta_reduce_prog p"
  shows "beta_reduced' (beta_reduce' p)" and "beta_reduce_prog\<^sup>*\<^sup>* p (beta_reduce' p)"
proof -
  have exq: "\<exists>q. beta_reduced' q \<and> beta_reduce_prog\<^sup>*\<^sup>* p q"
    using assms apply (induction, simp)
    by (metis beta_reduced'_def converse_rtranclp_into_rtranclp eq_imp_rtranclp)
  have "beta_reduced' (beta_reduce' p) \<and> beta_reduce_prog\<^sup>*\<^sup>* p (beta_reduce' p)" (is "?P (beta_reduce' p)")
    unfolding beta_reduce'_def 
    apply (subst exq, subst exq, simp)
    by (rule theI'[of ?P], auto intro: exq beta_unique')
  thus "beta_reduced' (beta_reduce' p)" and "beta_reduce_prog\<^sup>*\<^sup>* p (beta_reduce' p)"
    by auto
qed

lemma beta_reduceI:
  assumes "beta_reduced q" and "beta_reduce_proc\<^sup>*\<^sup>* p q"
  shows "beta_reduce p = q"
unfolding beta_reduce_def using assms apply auto
by (metis (mono_tags, lifting) beta_unique theI')

lemma beta_reduceI':
  assumes "beta_reduced' q" and "beta_reduce_prog\<^sup>*\<^sup>* p q"
  shows "beta_reduce' p = q"
unfolding beta_reduce'_def using assms apply auto
by (metis (mono_tags, lifting) beta_unique' theI')

lemmas well_typed_beta_reduce = beta_reduce_proofs.well_typed_beta_reduce

lemma beta_reduce_preserves_well_typed:
  assumes "well_typed_proc'' E p T"
  shows "well_typed_proc'' E (beta_reduce p) T"
proof -
  have "beta_reduce_proc\<^sup>*\<^sup>* p (beta_reduce p)"
    by (metis assms beta_reduce_def2(2) well_typed_beta_reduce(2))
  moreover {fix q have "beta_reduce_proc\<^sup>*\<^sup>* p q \<Longrightarrow> well_typed_proc'' E q T"
    apply (induction rule:rtranclp_induct)
    close (fact assms)
    by (rule subject_reduction, simp_all)}
  ultimately show ?thesis by simp
qed

lemma beta_reduce_rewrite:
  assumes "termip beta_reduce_proc p"
  and "beta_reduce_proc\<^sup>*\<^sup>* p q"
  shows "beta_reduce p = beta_reduce q"
by (metis accp_downwards_aux assms(1) assms(2) beta_reduce_def2(1) beta_reduce_def2(2) beta_unique rtranclp_converseI rtranclp_trans)

lemma beta_reduce_ProcAbs:
  assumes "well_typed_proc'' E p T"
  shows "beta_reduce (ProcAbs p) = ProcAbs (beta_reduce p)"
proof -
  have "beta_reduce_proc\<^sup>*\<^sup>* p (beta_reduce p)"
    apply (rule beta_reduce_def2) apply (rule well_typed_beta_reduce) using assms by auto
  hence "beta_reduce_proc\<^sup>*\<^sup>* (ProcAbs p) (ProcAbs (beta_reduce p))"
    by (metis beta_reduce_proofs.rtrancl_beta_ProcAbs)
  moreover have "beta_reduced (ProcAbs (beta_reduce p))"
    by (metis (full_types) assms beta_reduce_def2(1) well_typed_beta_reduce(2) beta_reduced_def brc_ProcAbs)
  ultimately show ?thesis
    by (rule beta_reduceI[rotated])
qed
  
lemma beta_reduce_Proc:
  assumes "well_typed'' E body"
  shows "beta_reduce (Proc body args ret) = Proc (beta_reduce' body) args ret"
proof -
  have "beta_reduce_prog\<^sup>*\<^sup>* body (beta_reduce' body)"
    apply (rule beta_reduce'_def2) apply (rule well_typed_beta_reduce) using assms by auto
  hence "beta_reduce_proc\<^sup>*\<^sup>* (Proc body args ret) (Proc (beta_reduce' body) args ret)"
    by (metis beta_reduce_proofs.rtrancl_beta_Proc)
  moreover have "beta_reduced' (beta_reduce' body)" 
    apply (rule beta_reduce'_def2) apply (rule well_typed_beta_reduce) using assms by auto
  have "beta_reduced (Proc (beta_reduce' body) args ret)"
    by (metis `beta_reduced' (beta_reduce' body)` beta_reduced'_def beta_reduced_def brc_Proc)
  ultimately show ?thesis
    by (rule beta_reduceI[rotated])
qed

lemma beta_reduce_beta:
  assumes "well_typed_proc'' (T#E) p U"
  assumes "well_typed_proc'' E q T"
  shows "beta_reduce (ProcAppl (ProcAbs p) q) = beta_reduce (subst_proc 0 q p)"
proof -
  have "termip beta_reduce_proc (ProcAppl (ProcAbs p) q)"
    apply (rule well_typed_beta_reduce)
    apply (rule wt_ProcAppl)
    apply (rule wt_ProcAbs)
    using assms .
  moreover have "beta_reduce_proc\<^sup>*\<^sup>* (ProcAppl (ProcAbs p) q) (subst_proc 0 q p)"
    by (metis br_beta r_into_rtranclp)
  ultimately show ?thesis
    by (rule beta_reduce_rewrite)
qed
  
definition "apply_procedure p a = beta_reduce (ProcAppl p a)"

lemma well_typed_well_typed'': 
  shows "well_typed p \<Longrightarrow> well_typed'' [] p"
  apply (induction rule:well_typed.induct) close (auto simp: wt_Seq)
  close (simp add: wt_Assign) close (simp add: wt_Sample) close (simp add: wt_Skip)
  close (simp add: wt_While) close (simp add: wt_IfTE) close (simp add: wt_CallProc wt_Proc)
  by auto

lemma well_typed_proc_well_typed_proc'':
  shows "well_typed_proc p \<Longrightarrow> well_typed_proc'' [] p (ProcTSimple (proctype_of p))"
apply (cases p, auto) apply (rule wt_Proc, auto) by (rule well_typed_well_typed'', simp)

lemma well_typed_proc_beta_reduced: 
  shows "well_typed_proc p \<Longrightarrow> beta_reduced p"
SORRY

lemma well_typed_proc''_well_typed:
  assumes "well_typed_proc'' [] p (ProcTSimple T)"
  assumes "beta_reduced p"
  shows "well_typed_proc p" and "proctype_of p = T"
SORRY

lemma well_typed_not_ProcAppl_ProcUnpair:
  fixes p1 p2 T
  assumes p: "p = ProcAppl p1 p2 \<or> p = ProcUnpair b p1"
  assumes wt: "well_typed_proc'' [] p T"
  assumes red: "beta_reduced p"
  shows False
proof -
  {fix Ta U p1 p2
   assume wt_p1: "well_typed_proc'' [] p1 (ProcTFun Ta U)"
   assume p1_IH: "\<And>p1a p2 b. beta_reduced p1 \<Longrightarrow> p1 = ProcAppl p1a p2 \<or> p1 = ProcUnpair b p1a \<Longrightarrow> False"
   assume wt_p2: "well_typed_proc'' [] p2 Ta"
   assume p2_IH: "\<And>p1 p2a b. beta_reduced p2 \<Longrightarrow> p2 = ProcAppl p1 p2a \<or> p2 = ProcUnpair b p1 \<Longrightarrow> False"
   assume red_app: "beta_reduced (ProcAppl p1 p2)"
  have red_p1: "beta_reduced p1"
    by (metis red_app beta_reduced_def br_ProcAppl1)
  obtain p1' where pa: "p1 = ProcAbs p1'"
    apply atomize_elim using wt_p1 apply cases apply auto
    apply (metis p1_IH red_p1)
    by (metis p1_IH red_p1)
  have "beta_reduce_proc (ProcAppl p1 p2) (subst_proc 0 p2 p1')"
    unfolding pa by (rule br_beta)
  with red_app have False unfolding beta_reduced_def by metis
  } note appl = this

  {fix Ta U p1 ba
  assume wt_p1: "well_typed_proc'' [] p1 (ProcTPair Ta U)"
  assume IH: "\<And>p1a p2 b. beta_reduced p1 \<Longrightarrow> p1 = ProcAppl p1a p2 \<or> p1 = ProcUnpair b p1a \<Longrightarrow> False"
  assume red_unpair: "beta_reduced (ProcUnpair ba p1)"
  have red_p1: "beta_reduced p1"
    by (metis (full_types) beta_reduced_def br_ProcUnpair red_unpair)
  obtain p1a p1b where p1: "p1 = ProcPair p1a p1b"
    apply atomize_elim using wt_p1 apply cases apply auto
    close (metis IH red_p1)
    by (metis IH red_p1)
  have "beta_reduce_proc (ProcUnpair ba p1) (if ba then p1a else p1b)"
    unfolding p1 by (rule br_ProcUnpairPair)
  with red_unpair have False unfolding beta_reduced_def by metis
  } note unpair = this

  def E=="[]::procedure_type_open list"
  show False
    apply (insert red, insert p, insert E_def) using wt[folded E_def]
    apply (induction arbitrary: p1 p2 b taking: "\<lambda>x y. True", auto)
    using appl close metis
    using unpair by metis
qed

lemma well_typed_ProcTSimple_Proc:
  assumes "well_typed_proc'' [] p (ProcTSimple T)"
  assumes "beta_reduced p"
  obtains body args ret where "p = Proc body args ret"
SORRY

lemma well_typed_ProcTPair_ProcPair:
  assumes wt: "well_typed_proc'' [] p (ProcTPair T U)"
  assumes red: "beta_reduced p"
  obtains p1 p2 where "p = ProcPair p1 p2"
apply atomize_elim
using wt apply (cases, auto) 
using red close (metis well_typed_not_ProcAppl_ProcUnpair) 
using red by (metis well_typed_not_ProcAppl_ProcUnpair)

lemma beta_reduce_idem [simp]: "beta_reduce (beta_reduce x) = x"
  sorry


(* Undoing syntax changes introduced by Lambda and LambdaType *)
declare [[syntax_ambiguity_warning = true]]
(*
no_syntax "\<^const>TypedLambda.dB.App" :: "dB\<Rightarrow>dB\<Rightarrow>dB" (infixl "\<degree>" 200)
no_syntax "\<^const>TypedLambda.subst" :: "[dB, dB, nat] => dB"  ("_[_'/_]" [300, 0, 0] 300)
no_syntax "\<^const>TypedLambda.beta" :: "[dB, dB] => bool"  (infixl "\<rightarrow>\<^sub>\<beta>" 50)
no_syntax "\<^const>TypedLambda.beta_reds" :: "[dB, dB] => bool"  (infixl "->>" 50)
no_syntax "\<^const>TypedLambda.beta_reds" :: "[dB, dB] => bool"  (infixl "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50)
no_syntax "\<^const>TypedLambda.shift" :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_<_:_>" [90, 0, 0] 91)
no_syntax "\<^const>TypedLambda.shift" :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<langle>_:_\<rangle>" [90, 0, 0] 91)
no_syntax "\<^const>TypedLambda.shift" :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<langle>_:_\<rangle>" [90, 0, 0] 91)
no_syntax "\<^const>TypedLambda.type.Fun" :: "TypedLambda.type \<Rightarrow> TypedLambda.type \<Rightarrow> TypedLambda.type"  (infixr "\<Rightarrow>" 200)
no_syntax "\<^const>TypedLambda.typing" :: "(nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile> _ : _" [50, 50, 50] 50)
no_syntax "\<^const>TypedLambda.typings_rel" :: "(nat \<Rightarrow> type) \<Rightarrow> dB list \<Rightarrow> type list \<Rightarrow> bool" ("_ ||- _ : _" [50, 50, 50] 50)
no_syntax "\<^const>TypedLambda.typings_rel" :: "(nat \<Rightarrow> type) \<Rightarrow> dB list \<Rightarrow> type list \<Rightarrow> bool" ("_ \<tturnstile> _ : _" [50, 50, 50] 50)
no_syntax "\<^const>TypedLambda.funs" :: "type list \<Rightarrow> type \<Rightarrow> type"  (infixr "=>>" 200)
no_syntax "\<^const>TypedLambda.funs" :: "type list \<Rightarrow> type \<Rightarrow> type"  (infixr "\<Rrightarrow>" 200)
*)

end


