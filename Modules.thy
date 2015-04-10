theory Modules
imports Lang_Typed TermX_Antiquot
begin


datatype procedure_type_open = ProcSimple procedure_type | ProcFun procedure_type_open procedure_type_open
fun ProcFun' where
  "ProcFun' [] T = T"
| "ProcFun' (T#Ts) U = ProcFun T (ProcFun' Ts U)"

(*datatype procedure_type_open = ProcTypeOpen "procedure_type_open list" "procedure_type"*)

fun nth_opt :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "nth_opt (x#xs) 0 = Some x"
| "nth_opt (x#xs) (Suc n) = nth_opt xs n"
| "nth_opt [] _ = None"

lemma list_all2_mono' [mono]: "A \<le> B \<Longrightarrow> list_all2 A \<le> list_all2 B"
  apply auto unfolding list_all2_iff by auto

(*lemma case_ProcTypeOpen_mono: "A \<le> B \<Longrightarrow> (case t of ProcTypeOpen e T \<Rightarrow> A e T) \<le> (case t of ProcTypeOpen e T \<Rightarrow> B e T)"
  by (cases t, simp add: le_fun_def)
lemma case_ProcTypeOpen_mono': "A \<le> B \<Longrightarrow> Modules.procedure_type_open.case_procedure_type_open A \<le> Modules.procedure_type_open.case_procedure_type_open B"
  unfolding le_fun_def apply auto
  apply (case_tac "x::procedure_type_open")
  by (simp add: le_fun_def)*)



(*
inductive well_typed'' :: "procedure_type_open list \<Rightarrow> program_rep \<Rightarrow> bool"
and well_typed_proc'' :: "procedure_type_open list \<Rightarrow> procedure_rep \<Rightarrow> bool" where
  wt_Seq: "well_typed'' E p1 \<and> well_typed'' E p2 \<Longrightarrow> well_typed'' E (Seq p1 p2)"
| wt_Assign: "eu_type e = vu_type v \<Longrightarrow> well_typed'' E (Assign v e)"
| wt_Sample: "ed_type e = vu_type v \<Longrightarrow> well_typed'' E (Sample v e)"
| wt_Skip: "well_typed'' E Skip"
| wt_While: "eu_type e = bool_type \<Longrightarrow> well_typed'' E p \<Longrightarrow> well_typed'' E (While e p)"
| wt_IfTE: "eu_type e = bool_type \<Longrightarrow> well_typed'' E thn \<Longrightarrow>  well_typed'' E els \<Longrightarrow> well_typed'' E (IfTE e thn els)"
| wt_CallProc: "vu_type v = pt_returntype (proctype_of prc) \<Longrightarrow>
   list_all2 (\<lambda>e T. eu_type e = T) args (pt_argtypes (proctype_of prc)) \<Longrightarrow>
   well_typed_proc'' E prc \<Longrightarrow>
   well_typed'' E (CallProc v prc args)"
(*| wt_ProcRef: "nth_opt E i = Some(ProcTypeOpen pi_envT pi_t) \<Longrightarrow> 
   length pi_envT = length env \<Longrightarrow>
   list_all2 (\<lambda>T p. case T of ProcTypeOpen _ T \<Rightarrow> proctype_of p = T) pi_envT env \<Longrightarrow>
   list_all2 (\<lambda>T p. (\<lambda>e. well_typed_proc'' e p) (case T of ProcTypeOpen e _ \<Rightarrow> e)) pi_envT env  \<Longrightarrow>
   pi_t = \<lparr> pt_argtypes=argtypes, pt_returntype=returntype \<rparr> \<Longrightarrow>
   well_typed_proc'' E (ProcRef i env argtypes returntype)"
*)
| wt_ProcRef: "
  nth_opt E i = Some(ProcTypeOpen Ei_E Ei_T) \<Longrightarrow>
  (\<And>x. x\<in>set env \<Longrightarrow> wt_ProcRef E x) \<Longrightarrow>
  (list_all2 well_typed_proc'' Ei_E env) \<Longrightarrow>
  well_typed_proc'' E (ProcRef i env argtypes returntype)"
| wt_Proc: "well_typed'' E body \<Longrightarrow>
   list_all (\<lambda>v. \<not> vu_global v) pargs \<Longrightarrow>
   distinct pargs \<Longrightarrow>
   well_typed_proc'' E (Proc body pargs ret)"
*)


(*
function (sequential) well_typed'' :: "procedure_type_open list \<Rightarrow> program_rep \<Rightarrow> bool" 
and well_typed_proc'' :: "procedure_type_open list \<Rightarrow> procedure_rep \<Rightarrow> bool" where
  "well_typed'' E (Seq p1 p2) = (well_typed'' E p1 \<and> well_typed'' E p2)"
| "well_typed'' E (Assign v e) = (eu_type e = vu_type v)"
| "well_typed'' E (Sample v e) = (ed_type e = vu_type v)"
| "well_typed'' E Skip = True"
| "well_typed'' E (While e p) = ((eu_type e = bool_type) \<and> well_typed'' E p)"
| "well_typed'' E (IfTE e thn els) = ((eu_type e = bool_type) \<and> well_typed'' E thn \<and> well_typed'' E els)"
| "well_typed'' E (CallProc v prc args) =
    (let procT = proctype_of prc in
    vu_type v = pt_returntype procT \<and> 
    list_all2 (\<lambda>e T. eu_type e = T) args (pt_argtypes procT) \<and>
    well_typed_proc'' E prc)"
| "well_typed_proc'' E (ProcRef i env argtypes returntype) = 
    (case nth_opt E i of Some(ProcTypeOpen pi_envT pi_t) \<Rightarrow>
    length pi_envT = length env \<and>
    (\<forall>(T,p)\<in>set (zip pi_envT env). case T of ProcTypeOpen e T \<Rightarrow> (proctype_of p = T 
                        \<and> well_typed_proc'' e p)) \<and>
    pi_t = \<lparr> pt_argtypes=argtypes, pt_returntype=returntype \<rparr>)"
| "well_typed_proc'' E (Proc body pargs ret) = 
    (well_typed'' E body \<and> list_all (\<lambda>v. \<not> vu_global v) pargs \<and> distinct pargs)" by pat_completeness auto
print_theorems
termination apply (relation "measure (\<lambda>x. case x of 
  Inl(E,p) \<Rightarrow> size_list size(E) + size(p)
| Inr(E,p) \<Rightarrow> size_list size(E) + size(p))", auto)
proof -
  fix E e pi_envT::"procedure_type_open list" and p::procedure_rep and
      env::"procedure_rep list"
      and i::nat and pi_T T
  {fix l::"'a::size list" and n and s have "size_option size (nth_opt l n) \<le> size_list size l"
    apply (induction l arbitrary: n, auto)
    apply (case_tac n, auto)
    by (metis le_SucI trans_le_add2)}
  note nth_size = this
  assume ass1: "nth_opt E i = Some (ProcTypeOpen pi_envT pi_T)"
  have "size_option size (Some (ProcTypeOpen pi_envT pi_T)) \<le> size_list size E"
  thm size_option_def
    unfolding ass1[symmetric] by (rule nth_size)
  hence "size (ProcTypeOpen pi_envT pi_T) < size_list size E"
    by auto
  hence size_pi_envT: "size_list size pi_envT < size_list size E" by auto
  assume zip: "(ProcTypeOpen e T, p) \<in> set (zip pi_envT env)"
  hence "ProcTypeOpen e T \<in> set pi_envT"
    by (metis in_set_zipE)
  hence "size (ProcTypeOpen e T) \<le> size_list size pi_envT" apply auto
    by (metis add_Suc_right eq_iff monoid_add_class.add.right_neutral procedure_type_open.size(2) size_list_estimation')
  with size_pi_envT have "size (ProcTypeOpen e T) < size_list size E" by auto
  hence "size_list size e < size_list size E" by auto
  moreover from zip have "p\<in>set env" by (metis in_set_zipE)
  hence "size p \<le> size_list size env"
    by (metis order_refl size_list_estimation') 
  ultimately
  show "size_list size e + size p < Suc (size_list size E + size_list size env)" by auto
qed
*)

ML Term.betapply
declare[[show_types=false]]

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

(*
fun subst_proc_in_prog :: "procedure_rep list \<Rightarrow> program_rep \<Rightarrow> program_rep"
and subst_proc :: "procedure_rep list \<Rightarrow> procedure_rep \<Rightarrow> procedure_rep"
where
  subst_proc_Skip: "subst_proc_in_prog insts Skip = Skip"
| subst_proc_Seq: "subst_proc_in_prog insts (Seq p1 p2) = Seq (subst_proc_in_prog insts p1) (subst_proc_in_prog insts p2)"
| subst_proc_IfTE: "subst_proc_in_prog insts (IfTE c p1 p2) = IfTE c (subst_proc_in_prog insts p1) (subst_proc_in_prog insts p2)"
| subst_proc_While: "subst_proc_in_prog insts (While c p) = While c (subst_proc_in_prog insts p)"
| subst_proc_CallProc: "subst_proc_in_prog insts (CallProc v p e) = CallProc v (subst_proc insts p) e"
| subst_proc_Assign: "subst_proc_in_prog insts (Assign v e) = Assign v e"
| subst_proc_Sample: "subst_proc_in_prog insts (Sample v e) = Sample v e"
| subst_proc_Proc: "subst_proc insts (Proc body args ret) = Proc (subst_proc_in_prog insts body) args ret"
| subst_proc_ProcRef: "subst_proc insts (ProcRef i) =
    (if i<length insts then insts!i
    else ProcRef (i-length insts) n)"
| subst_proc_ProcAppl: "subst_proc insts (ProcAppl (ProcAbs p) q) =
  subst_procs (q#insts) p"
| subst_proc_ProcAbs: "subst_proc insts (ProcAbs p) = undefined"
print_theorems
*)

(*
E \<turnstile> q:u   E,u \<turnstile> p:t
-------------------
E \<turnstile> p$q : t

subst inst p$q = subst (subst inst q, inst) p

E!i = (F\<Rightarrow>t)
--------------------------
E@F \<turnstile> Ref i -drop- |E| : t

subst inst (Ref i -drop- n) = 
  subst (drop n inst) inst!i

q(a,b) = a(b)
r(a) = q(a,a)
r(r) = q(r,r) = r(r) infinity

q(a) = a = Ref0-1
subst [x] q = x

r(q,a) = q $ a = Ref0-2 $ Ref1-2

subst [q,y] r =
  subst [q,y] (Ref0-2 $ Ref1-2)
= subst [subst [q,y] Ref1-2,q,y] Ref0-2
= subst [subst [] y,q,y] Ref0-2


p(q) = r(q,a) = 

E,t \<turnstile> p:u
----------
E \<turnstile> %.p : t\<Rightarrow>u

E \<turnstile> p:t   E \<turnstile> q:t\<Rightarrow>u
--------------------
E \<turnstile> q$p : u

---------------
E \<turnstile> Ref i : E_i


q(a) = a(d)
 = (Ref 0) -inst- d
 = %a. a d
 = %. 0 d

p(a,b) = q(a(b))
 = q -inst- (Ref2 -inst- Ref0)
 = %a %b. q $ (a $ b)
 = %%. q $ 1 $ 0

Ref i = Bound i
A -inst- B \<equiv> (\<lambda>x. A) B

*)

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



abbreviation "beta_reduce_prog_dom pg == beta_reduce_prog_beta_reduce_proc_dom(Inl pg)"
abbreviation "beta_reduce_proc_dom pc == beta_reduce_prog_beta_reduce_proc_dom(Inr pc)"

fun R :: "procedure_type_open \<Rightarrow> procedure_rep \<Rightarrow> bool" where
  "R (ProcSimple T) p = (beta_reduce_proc_dom p \<and> well_typed_proc'' [] p (ProcSimple T))"
| "R (ProcFun T U) p = (beta_reduce_proc_dom p \<and> well_typed_proc'' [] p (ProcFun T U) \<and>
  (\<forall>p'. R T p' \<longrightarrow> R U (ProcAppl p p')))"

lemma well_typed_lift:
  assumes "well_typed_proc'' (F@E) q T"
  shows "well_typed_proc'' (F@U#E) (lift_proc q (length F)) T"
proof -
  have "\<And>T F. well_typed'' (F@E) pg \<Longrightarrow> well_typed'' (F@T#E) (lift_proc_in_prog pg (length F))"
   and res:"\<And>T U F. well_typed_proc'' (F@E) q U \<Longrightarrow> well_typed_proc'' (F@T#E) (lift_proc q (length F)) U"
  proof (induct pg and q) 
  case Assign thus ?case by (auto simp: wt_Assign_iff[symmetric])
  next case Sample thus ?case by (auto simp: wt_Sample_iff[symmetric])
  next case (Proc body args ret) thus ?case by (auto simp: wt_Proc_iff[symmetric])
  next case (CallProc v p a U) thus ?case by (auto simp: wt_CallProc_iff[symmetric])
  next case Seq thus ?case by (auto simp: wt_Seq_iff[symmetric])
  next case Skip thus ?case by (auto simp: wt_Skip)
  next case IfTE thus ?case by (auto simp: wt_IfTE_iff[symmetric])
  next case While thus ?case by (auto simp: wt_While_iff[symmetric])
  next case (ProcRef n)
    have nth: "nth_opt (F @ T # E) (length F) = Some T"
      by (induct F, auto)
    have nth2: "\<And>n. length F < n \<Longrightarrow> nth_opt (F@T#E) n = nth_opt (F@E) (n - Suc 0)"
      apply (induct F arbitrary: n, case_tac n, auto)
      apply (case_tac n, auto)
      by (metis Suc_pred gr0_conv_Suc lessE nth_opt.simps(2)) 
    have nth3: "n < length F \<Longrightarrow> nth_opt (F@T#E) n = nth_opt (F @ E) n"
      apply (induct F arbitrary: n, auto)
      by (case_tac n, auto)
    from ProcRef show ?case apply (auto simp: wt_ProcRef_iff[symmetric] nth3)
      by (subst nth2, auto)
  next case (ProcAbs p T U) 
    from ProcAbs.prems obtain U1 U2 where U:"U=ProcFun U1 U2"
      and wt: "well_typed_proc'' (U1#F@E) p U2"
      unfolding wt_ProcAbs_iff[symmetric] by auto
    show ?case apply (simp add: wt_ProcAbs_iff[symmetric]) 
      apply (rule exI[of _ U1], rule exI[of _ U2], simp add: U)
      apply (rule ProcAbs.hyps[where F="U1#F" and T=T and U=U2, simplified])
      by (fact wt)
  next case (ProcAppl p1 p2 ) thus ?case by (auto simp: wt_ProcAppl_iff[symmetric], metis)
  qed
  from res assms show ?thesis .
qed
  
lemma well_typed_subst':
  assumes "well_typed_proc'' (F@E) q T"
  shows "well_typed'' (F@T#E) pg \<Longrightarrow> well_typed'' (F@E) (subst_proc_in_prog (length F) q pg)"
  and "well_typed_proc'' (F@T#E) p U \<Longrightarrow> well_typed_proc'' (F@E) (subst_proc (length F) q p) U"
proof -
  fix pg
  have res:"\<And>T E F q.
    well_typed'' (F@T#E) pg \<Longrightarrow>
    well_typed_proc'' (F@E) q T \<Longrightarrow>
    well_typed'' (F@E) (subst_proc_in_prog (length F) q pg)"
   and  "\<And>T U E F q.
    well_typed_proc'' (F@T#E) p U \<Longrightarrow>
    well_typed_proc'' (F@E) q T \<Longrightarrow>
    well_typed_proc'' (F@E) (subst_proc (length F) q p) U"
  proof (induct pg and p)
    case Assign thus ?case by (auto simp: wt_Assign_iff[symmetric])
    next case Sample thus ?case by (auto simp: wt_Sample_iff[symmetric])
    next case Proc thus ?case by (auto simp: wt_Proc_iff[symmetric])
    next case (ProcRef n) 
      have nth: "nth_opt (F @ T # E) (length F) = Some T"
        by (induct F, auto)
      have tmp: "\<And>x l m. x#l@m = (x#l)@m" by auto
      have nth2: "length F < n \<Longrightarrow> nth_opt (F@T#E) n = nth_opt (F@E) (n - Suc 0)"
        apply (induct F arbitrary: n, case_tac n, auto)
        apply (case_tac n, auto)
        by (metis Suc_pred gr0_conv_Suc lessE nth_opt.simps(2)) 
      have nth3: "n < length F \<Longrightarrow> nth_opt (F@T#E) n = nth_opt (F @ E) n"
        apply (induct F arbitrary: n, auto)
        by (case_tac n, auto)
      from ProcRef show ?case by (auto simp: wt_ProcRef_iff[symmetric] nth nth2 nth3)
    next case (ProcAppl p1 p2)
      from ProcAppl.prems(1) obtain T' where 
        wt1: "well_typed_proc'' (F@T#E) p1 (ProcFun T' U)" and wt2: "well_typed_proc'' (F@T#E) p2 T'"
        unfolding wt_ProcAppl_iff[symmetric] by auto
      have wt1': "well_typed_proc'' (F@E) (subst_proc (length F) q p1) (ProcFun T' U)"
        by (rule ProcAppl, rule wt1, rule ProcAppl)
      have wt2': "well_typed_proc'' (F@E) (subst_proc (length F) q p2) T'"
        by (rule ProcAppl, rule wt2, rule ProcAppl)
      show ?case apply simp
        unfolding wt_ProcAppl_iff[symmetric] apply (rule exI[of _ T']) using wt1' wt2' by auto
    next case Seq thus ?case by (auto simp: wt_Seq_iff[symmetric])
    next case Skip show ?case by (simp, rule wt_Skip)
    next case IfTE thus ?case by (auto simp: wt_IfTE_iff[symmetric])
    next case While thus ?case by (auto simp: wt_While_iff[symmetric])
    next case CallProc thus ?case by (auto simp: wt_CallProc_iff[symmetric])
    next case (ProcAbs p)
      from ProcAbs.prems obtain T' U' where U: "U = ProcFun T' U'" and wt: "well_typed_proc'' (T' # F @ T # E) p U'" 
        unfolding wt_ProcAbs_iff[symmetric] by auto  
      show ?case apply simp
        unfolding wt_ProcAbs_iff[symmetric]
        apply (rule exI[of _ T'], rule exI[of _ U'], auto simp: U wt)
        apply (rule ProcAbs.hyps[of "T'#F", simplified])
        apply (fact wt) 
        apply (rule well_typed_lift[where F="[]", simplified])
        by (fact ProcAbs.prems)
    qed
  with assms
  show "well_typed'' (F@T#E) pg \<Longrightarrow> well_typed'' (F@E) (subst_proc_in_prog (length F) q pg)"
  and "well_typed_proc'' (F@T#E) p U \<Longrightarrow> well_typed_proc'' (F@E) (subst_proc (length F) q p) U"
    by auto
qed

lemma well_typed_subst:
  assumes "well_typed_proc'' (F@E) q T"
  assumes "well_typed'' (F@T#E) pg"
  shows "well_typed'' (F@E) (subst_proc_in_prog (length F) q pg)"
using assms by (rule well_typed_subst')

lemma well_typed_proc_subst:
  assumes "well_typed_proc'' (F@E) q T"
  assumes "well_typed_proc'' (F@T#E) p U"
  shows "well_typed_proc'' (F@E) (subst_proc (length F) q p) U"
using assms by (rule well_typed_subst')

lemma nth_opt_prefix: "nth_opt F n = Some T \<Longrightarrow> nth_opt (F @ E) n = Some T"
  apply (induction F arbitrary: n, auto)
  by (case_tac n, auto)


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
    next case ProcRef thus ?case apply (auto simp: wt_ProcRef_iff[symmetric])
      by (rule nth_opt_prefix)
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

lemma well_typed_subst_proc_dom:
(*  assumes "well_typed_proc'' E p T"*)
  shows "beta_reduce_proc_dom p"
proof -
  have R_term: "\<And>T p. R T p \<Longrightarrow> beta_reduce_proc_dom p"
    by (case_tac T, simp_all)
  {fix p E F v have "list_all2 (well_typed_proc'' []) v E \<Longrightarrow> well_typed'' E p
        \<Longrightarrow> well_typed'' [] (fold (subst_proc_in_prog 0) v p)"
    proof (induction arbitrary: p rule:list_all2_induct)
    case Nil thus ?case by auto next
    case (Cons v1 v E1 E) show ?case apply simp
      apply (rule Cons.IH)
      apply (rule well_typed_subst[where F="[]" and T=E1, simplified])
      apply (rule well_typed_extend)
      apply (fact Cons.hyps)
      by (fact Cons.prems)
    qed}
  hence well_typed_subst': "\<And>v E p. list_all2 (well_typed_proc'' []) v (rev E) \<Longrightarrow> well_typed'' E p
        \<Longrightarrow> well_typed'' [] (foldr (subst_proc_in_prog 0) v p)"
     unfolding foldr_conv_fold 
     unfolding list_all2_rev1[symmetric] .
  note well_typed_subst_list = this

  have "well_typed'' E pg \<Longrightarrow> list_all2 R E (rev v) \<Longrightarrow> beta_reduce_prog_dom (foldr (subst_proc_in_prog 0) v pg)"
   and "well_typed_proc'' E p T \<Longrightarrow>
        (\<And>v. list_all2 R E (rev v) \<Longrightarrow>
              R T (foldr (subst_proc 0) v p))" 
  proof (induction E pg and E p T arbitrary:v rule:well_typed''_well_typed_proc''.inducts)
  case (wt_Seq E p1 p2) 
    have com: "foldr (subst_proc_in_prog 0) v (Seq p1 p2) = Seq (foldr (subst_proc_in_prog 0) v p1) (foldr (subst_proc_in_prog 0) v p2)"
      apply (subst foldr_conv_fold)
      by (induct v, auto)
    show ?case by (auto simp: com wt_Seq beta_reduce_prog_beta_reduce_proc.domintros)
  next case (wt_While c E p)
    have com: "foldr (subst_proc_in_prog 0) v (While c p) = While c (foldr (subst_proc_in_prog 0) v p)"
      by (induct v, auto)
    show ?case by (auto simp: com beta_reduce_prog_beta_reduce_proc.domintros)
  next case (wt_Assign e x)
    have com: "foldr (subst_proc_in_prog 0) v (Assign x e) = Assign x e"
      by (induct v, auto)
    show ?case by (auto simp: com wt_Assign beta_reduce_prog_beta_reduce_proc.domintros)
  next case (wt_Sample e x)
    have com: "foldr (subst_proc_in_prog 0) v (Sample x e) = Sample x e"
      by (induct v, auto)
    show ?case by (auto simp: com wt_Sample beta_reduce_prog_beta_reduce_proc.domintros)
  next case (wt_CallProc E prc args x)
    have com: "foldr (subst_proc_in_prog 0) v (CallProc x prc args) = CallProc x (foldr (subst_proc 0) v prc) args"
      by (induct v, auto)
    show ?case
      using wt_CallProc by (auto simp: com beta_reduce_prog_beta_reduce_proc.domintros)
  next case (wt_Proc E body pargs ret v) term ?case
    have com: "foldr (subst_proc 0) v (Proc body pargs ret) = Proc (foldr (subst_proc_in_prog 0) v body) pargs ret"
      by (induct v, auto)
    have l:"list_all2 (well_typed_proc'' []) v (rev E)"
      apply (subst list_all2_swap)
      apply (rule list_all2_mono[where P=R])
      apply (unfold list_all2_rev1)
      apply (fact wt_Proc.prems)
      by (metis R.simps procedure_type_open.exhaust)
    show ?case 
      apply (auto simp: com)
      apply (rule beta_reduce_prog_beta_reduce_proc.domintros)
      using wt_Proc apply simp
      apply (rule Modules.wt_Proc)
      apply (rule well_typed_subst', fact l, fact wt_Proc.hyps)
      apply (simp add: wt_Proc)
      by (simp add: wt_Proc)
  next case wt_Skip
    have com: "foldr (subst_proc_in_prog 0) v Skip = Skip"
      by (induct v, auto)
    thus ?case by (auto simp: com beta_reduce_prog_beta_reduce_proc.domintros)
  next case (wt_IfTE e E p1 p2) 
    have com: "foldr (subst_proc_in_prog 0) v (IfTE e p1 p2) = IfTE e (foldr (subst_proc_in_prog 0) v p1) (foldr (subst_proc_in_prog 0) v p2)"
      by (induct v, auto)
    show ?case by (auto simp: com beta_reduce_prog_beta_reduce_proc.domintros)

  next case (wt_ProcRef E i T v) 
    {fix E::"procedure_type_open list" and i T have "nth_opt E i = Some T \<Longrightarrow> \<not> length E \<le> i"
      by (induct E i rule:nth_opt.induct, auto)}
    note nth = this
    {fix E p T x i have "well_typed'' E pg \<Longrightarrow> i\<ge>length E \<Longrightarrow> subst_proc_in_prog i x pg = pg"
     and "well_typed_proc'' E p T \<Longrightarrow> i\<ge>length E \<Longrightarrow> subst_proc i x p = p"
      apply (induct arbitrary: i x and i x rule:well_typed''_well_typed_proc''.inducts, auto simp: nth)
      by (metis le_trans less_imp_le_nat nth)}
    from this[of "[]"] 
    have wt_sub: "\<And>i x p T. well_typed_proc'' [] p T \<Longrightarrow> subst_proc i x p = p" by auto
    have "\<forall>p\<in>set v. \<exists>T. well_typed_proc'' [] p T"
      by (metis wt_ProcRef.prems R.elims(2) in_set_conv_nth list_all2_nthD2 list_all2_rev1)
    with wt_sub have inv:"\<And>x p. p\<in>set v \<Longrightarrow> subst_proc 0 x p = p" by metis
    hence inv2: "\<And>a vv. a\<in>set (rev v) \<Longrightarrow> fold (subst_proc 0) vv a = a"
      by (induct_tac vv, auto)
    have lenE: "length E > i" 
      apply (insert wt_ProcRef.hyps, induction E arbitrary: i)
      by (auto, case_tac i, auto)
    have lenV: "length v > i"
      by (metis wt_ProcRef.prems lenE length_rev list_all2_conv_all_nth)
    {fix v have "length v > i \<Longrightarrow> (\<And>a vv. a\<in>set (rev v) \<Longrightarrow> fold (subst_proc 0) vv a = a)
              \<Longrightarrow> foldr (subst_proc 0) (rev v) (ProcRef i) = v!i"
      apply (unfold foldr_conv_fold)
      by (induction v arbitrary: i, auto)}
    hence com: "foldr (subst_proc 0) v (ProcRef i) = (rev v)!i"
      using lenV inv2 by (metis length_rev rev_rev_ident set_rev) 
    {fix v have "nth_opt E i = Some T \<Longrightarrow> list_all2 R E v \<Longrightarrow> R T (v!i)"
      apply (induction v arbitrary: E i, auto, case_tac E, auto)
      by (metis not0_implies_Suc not_less0 nth_Cons_Suc nth_non_equal_first_eq nth_opt.simps(1) nth_opt.simps(2) option.inject)}
    hence ?case apply (auto simp: com) 
      using wt_ProcRef by auto 
  next case (wt_ProcAppl E p T U q)  term?case
    have com: "foldr (subst_proc 0) v (ProcAppl p q) = ProcAppl (foldr (subst_proc 0) v p) (foldr (subst_proc 0) v q)"
      by (induct v, auto)
    from wt_ProcAppl show ?case by (auto simp: com beta_reduce_prog_beta_reduce_proc.domintros)
  next case (wt_ProcAbs T E p U) term?case 
    have com: "foldr (subst_proc k) v (ProcAbs p) 
               = ProcAbs (foldr (subst_proc (Suc k)) (map (\<lambda>x. lift_proc x 0) v) p)"
      by (induct v, auto)
(* | subst_proc_ProcAbs: "subst_proc k s (ProcAbs t) = ProcAbs (subst_proc (Suc k) (lift_proc s 0) t)"
*)
    from wt_ProcAppl show ?case by (auto simp: com beta_reduce_prog_beta_reduce_proc.domintros)
  with assms show ?thesis
qed

  have "well_typed'' E pg \<Longrightarrow> beta_reduce_prog_dom pg"
   and "well_typed_proc'' E p T \<Longrightarrow> beta_reduce_proc_dom p"
 apply (induct E pg and E p T rule:well_typed''_well_typed_proc''.inducts)
 apply (simp_all add: beta_reduce_proc_in_prog_beta_reduce_proc.domintros)
 apply (rule beta_reduce_proc_in_prog_beta_reduce_proc.domintros, auto)

lemma well_typed_subst_proc:
  assumes "well_typed_proc'' E p T"
  shows "well_typed_proc'' E (beta_reduce_proc p) T"


(*
lemma wt_Seq_iff: "well_typed'' E (Seq p1 p2) = (well_typed'' E p1 \<and> well_typed'' E p2)"   
  by (rule iffI, cases rule:well_typed''.cases, auto, simp add: well_typed''_well_typed_proc''.intros)
lemma wt_IfTE_iff: "well_typed'' E (IfTE e thn els) = (eu_type e = bool_type \<and> well_typed'' E thn \<and>  well_typed'' E els)"
  by (rule iffI, cases rule:well_typed''.cases, auto, simp add: well_typed''_well_typed_proc''.intros)
lemma wt_Assign_iff: "well_typed'' E (Assign v e) = (eu_type e = vu_type v)"
  by (rule iffI, cases rule:well_typed''.cases, auto, simp add: well_typed''_well_typed_proc''.intros)
lemma wt_Sample_iff: "well_typed'' E (Sample v e) = (ed_type e = vu_type v)"
  by (rule iffI, cases rule:well_typed''.cases, auto, simp add: well_typed''_well_typed_proc''.intros)
lemma wt_While_iff: "well_typed'' E (While e p) = (eu_type e = bool_type \<and> well_typed'' E p)"
  by (rule iffI, cases rule:well_typed''.cases, auto, simp add: well_typed''_well_typed_proc''.intros)
lemma wt_CallProc_iff: "well_typed'' E (CallProc v prc args) = (\<exists>T. (vu_type v = pt_returntype T \<and>
   list_all2 (\<lambda>e T. eu_type e = T) args (pt_argtypes T) \<and>
   well_typed_proc'' (ProcTypeOpen E T) prc))"
  by (rule iffI, cases rule:well_typed''.cases, auto, simp add: well_typed''_well_typed_proc''.intros)
lemma wt_Proc_iff: "well_typed_proc'' (ProcTypeOpen E T) (Proc body pargs ret) =
  (well_typed'' E body \<and>
   list_all (\<lambda>v. \<not> vu_global v) pargs \<and>
   eu_type ret = pt_returntype T \<and>
   list_all2 (\<lambda>e T. vu_type e = T) pargs (pt_argtypes T) \<and>
   distinct pargs)"
  by (rule iffI, cases rule:well_typed_proc''.cases, auto, simp add: well_typed''_well_typed_proc''.intros)
lemma wt_ProcRef_iff: "well_typed_proc'' (ProcTypeOpen E U) (ProcRef i (ProcTypeOpen envT T)) =
  (T=U \<and> nth_opt E i = Some (ProcTypeOpen envT T))" 
  by (rule iffI, cases rule:well_typed_proc''.cases, auto, simp add: well_typed''_well_typed_proc''.intros)
lemma wt_ProcInst_iff: "well_typed_proc'' (ProcTypeOpen E' T) (ProcInst inst prc) =
  (\<exists>E instT. well_typed_proc'' (ProcTypeOpen E instT) inst \<and>
  well_typed_proc'' (ProcTypeOpen (ProcTypeOpen E instT#E') T) prc)"
  by (rule iffI, cases rule:well_typed_proc''.cases, auto, simp add: well_typed''_well_typed_proc''.intros)
*)

definition "module_type_rep_set envT proctypes \<equiv> {procs. list_all2 (\<lambda>T p. well_typed_proc'' [] p (ProcFun' envT (ProcSimple T))) proctypes procs}"
lemma module_type_rep_set_inhabited: "\<exists>x. x \<in> module_type_rep_set env procT"
  sorry

class module_type =
  fixes "module_type_procs" :: "'a \<Rightarrow> procedure_rep list"
  fixes "module_type_construct" :: "procedure_rep list \<Rightarrow> 'a"
  fixes "module_type_proc_names" :: "'a itself \<Rightarrow> id list"
  fixes "module_type_proc_types" :: "'a itself \<Rightarrow> procedure_type list"
  fixes "module_type_environment" :: "'a itself \<Rightarrow> procedure_type_open list"
  assumes "distinct (module_type_proc_names TYPE('a))"
  assumes "length (module_type_procs a) = length (module_type_proc_names TYPE('a))"
  assumes module_type_procs_welltyped: "list_all2 
          (\<lambda>T p. well_typed_proc'' [] p (ProcFun' (module_type_environment TYPE('a)) (ProcSimple T)))
          (module_type_proc_types TYPE('a)) (module_type_procs m)"
  assumes module_type_construct_inverse: 
      "list_all2 
          (\<lambda>T p. well_typed_proc'' [] p (ProcFun' (module_type_environment TYPE('a)) (ProcSimple T)))
          (module_type_proc_types TYPE('a)) procs
      \<Longrightarrow> module_type_procs (module_type_construct procs) = procs"
  assumes module_type_procs_inverse: "module_type_construct (module_type_procs m) = m"

class module_type_closed = module_type +
  assumes closed_module_type_empty: "module_type_environment TYPE('a) = []"

(*
definition "module_type_proc_types_open MT \<equiv> 
  map (ProcTypeOpen (module_type_environment MT)) (module_type_proc_types MT)"
*)

definition "module_type_instantiation (_::'mt::module_type itself) (_::'mtc::module_type_closed itself)
  == module_type_proc_names TYPE('mt) = module_type_proc_names TYPE('mtc)
   \<and> module_type_proc_types TYPE('mt) = module_type_proc_types TYPE('mtc)" 



lemma welltyped_subst_proc: 
  (* TODO assumptions *)
  shows "well_typed_proc'' (ProcTypeOpen envT T) (subst_proc insts p)"
proof -
  have "list_all2 well_typed_proc'' envT insts \<Longrightarrow>
        well_typed'' envT pg \<Longrightarrow>
        well_typed'' envT (subst_proc_in_prog insts pg)"
   and "list_all2 well_typed_proc'' envT insts \<Longrightarrow>
        (\<And>T. well_typed_proc'' (ProcTypeOpen envT T) p \<Longrightarrow>
        well_typed_proc'' (ProcTypeOpen envT T) (subst_proc insts p))"
  proof (induction insts pg and insts p rule:subst_proc_in_prog_subst_proc.induct)
  case 1 (* Skip *) show ?case by (simp add: wt_Skip) next
  case 2 (* Seq *) thus ?case by (simp add: wt_Seq_iff) next
  case 3 (* IfTE *) thus ?case by (simp add: wt_IfTE_iff) next
  case 4 (* While *) thus ?case by (simp add: wt_While_iff) next
  case (5 insts v p e) (* CallProc *) thus ?case by (auto simp: wt_CallProc_iff) next
  case 6 (* Assign *) thus ?case by (simp add: wt_Assign_iff) next
  case 7 (* Sample *) thus ?case by (simp add: wt_Sample_iff) next
  case 8 (* Proc *) thus ?case  by (simp add: wt_Proc_iff) next
  case (9 insts i instT) (* ProcRef *) thus ?case
    apply (cases instT)
    apply (simp add: wt_ProcRef_iff) 
    apply auto 
  next
  case 10 (* ProcInst *) thus ?case apply (auto simp: wt_ProcInst_iff) 
qed



ML_file "modules.ML"

ML {*
  Goal.prove @{context} ["x"] [] @{prop "x=x"} (fn _ => simp_tac @{context} 1)
  |> prop_of
*}

ML ListPair.zip

setup {*
fn thy => thy |> snd o
Modules.define_module_type {
  name = @{binding MT},
  arguments = [],
  procs = [{name = @{binding a}, typ = @{typ "(unit,int)procedure"}},
           {name = @{binding b}, typ = @{typ "(int*unit,int)procedure"}}]
}*}

thm MT.MAKE.b

(*
(* TODO move *)
lemma proctype_of_mk_procedure_untyped [simp]:
  fixes p :: "('a::procargs,'b::prog_type)procedure"
  shows "proctype_of (mk_procedure_untyped p) = procedure_type TYPE(('a::procargs,'b::prog_type)procedure)"
  sorry
*)

(*
(* TODO move *)
lemma well_typed''_mk_procedure_untyped [simp]:
  fixes p :: "('a::procargs,'b::prog_type)procedure"
  shows "well_typed_proc'' [] (mk_procedure_untyped p)"
  sorry
*)

(* TODO move *)
lemma mk_procedure_untyped_inverse [simp]: 
  "mk_procedure_typed (mk_procedure_untyped p) = p"
  SORRY

declare[[simp_trace=false]]
(*definition "MT_make == \<lambda>(p1::(unit,int)procedure) (p2::(int*unit,int)procedure).
  Abs_MT [mk_procedure_untyped p1, mk_procedure_untyped p2]"*)
(*lemma MT_MAKE_a: "MT.a (MT.MAKE a b) = a"
  apply (unfold MT.a_def MT.MAKE_def module_type_procs_MT_def)
  apply (subst Abs_MT_inverse)
  (* First goal *)
  (* apply (simp only: list.simps Set.ball_simps HOL.simp_thms Modules.proctype_of_mk_procedure_untyped) *)
  apply (simp add: subst_proc_empty module_type_rep_set_def)
  (* Second goal *)
  apply (simp add: subst_proc_empty)
done*)

lemma "MT.b (MT.MAKE undefined undefined) = undefined" by simp

thm MT.MAKE.a

declare[[ML_exception_trace=false]]

setup {* fn thy => thy |> 
Modules.define_module_type {
  name = @{binding MT2},
  procs = [{name = @{binding b}, typ = @{typ "(bool*unit,bool)procedure"}}],
  arguments = [{name = @{binding M}, typ = @{typ "MT"}}] 
} |> snd*}

thm MT2.INST_def

(*
abbreviation "subst_proc_in_prog_dom procs pg == subst_proc_in_prog_subst_proc_dom(Inl(procs,pg))"
abbreviation "subst_proc_dom procs pc == subst_proc_in_prog_subst_proc_dom(Inr(procs,pc))"
*)

(*definition "has_proctypeopen T p == case T of ProcTypeOpen e t \<Rightarrow> well_typed_proc'' e p \<and> proctype_of p = t" *)

lemma proctype_subst_proc:
  (* TODO: assumptions *)
  shows "list_all2 has_proctypeopen envT insts \<longrightarrow> 
  has_proctypeopen (ProcTypeOpen envT T) p \<longrightarrow>
  has_proctypeopen (ProcTypeOpen envT T) (subst_proc insts p)"
proof -
  have "list_all2 has_proctypeopen envT insts \<Longrightarrow>
         well_typed'' envT pg \<Longrightarrow>
         well_typed'' envT (subst_proc_in_prog insts pg)" and
        "(list_all2 has_proctypeopen envT insts \<Longrightarrow>
        has_proctypeopen (ProcTypeOpen envT T) p \<Longrightarrow>
        has_proctypeopen (ProcTypeOpen envT T) (subst_proc insts p))"
  proof (induction insts pg and insts p arbitrary: T rule:subst_proc_in_prog_subst_proc.induct)
  print_cases
  case 1 (* Skip *) show ?case by (simp add: wt_Skip) next
  case 2 (* Seq *) thus ?case by (simp add: wt_Seq_iff) next
  case 3 (* IfTE *) thus ?case by (simp add: wt_IfTE_iff) next
  case 4 (* While *) thus ?case by (simp add: wt_While_iff) next
  case 6 thus ?case by (simp add: wt_Assign_iff) next
  case (5 insts v p e) (* CallProc *) thus ?case apply simp
    unfolding wt_CallProc_iff has_proctypeopen_def 
    apply (rule conjI, simp)

apply (simp add: wt_CallProc_iff)
  apply auto

(*
| wt_CallProc: "vu_type v = pt_returntype (proctype_of prc) \<Longrightarrow>
   list_all2 (\<lambda>e T. eu_type e = T) args (pt_argtypes (proctype_of prc)) \<Longrightarrow>
   well_typed_proc'' E prc \<Longrightarrow>
   well_typed'' E (CallProc v prc args)"
*)
  
  case 7 thus ?case by (simp add: wt_Sample_iff) next


by (simp add: wt_CallProc_iff) next


  apply auto
  apply (rule wt_Proc)
  apply (subst t1)
  apply simp
apply (rule subst_proc_in_prog_subst_proc.induct[where 
  Q="\<lambda>insts p. list_all2 has_proctypeopen envT insts \<longrightarrow> 
  has_proctypeopen (ProgTypeOpen envT T) p \<longrightarrow>
  has_proctypeopen (ProgTypeOpen envT T) (subst_proc insts p)" and P="\<lambda>insts p. True"], simp_all)
apply (case_tac T, simp)
apply TODO: need well_typedness in IH

declare[[show_consts]]
thm MT2.INST_def
(*definition "MT2_INST == \<lambda>MT2::MT2. \<lambda>MT::MT.
  Abs_MT2_instantiated (map (subst_proc (module_type_procs MT)) (module_type_procs MT2))" *)
lemma "MT2_instantiated.b (MT2.INST MT2 MT) = MT2.b MT2 MT"
  unfolding MT2.INST_def MT2_instantiated.b_def
  apply (subst module_type_construct_inverse)
  unfolding module_type_proc_types_MT2_instantiated_def
  apply simp 
  using module_type_procs1 module_type_procs2
  apply auto
  sorry


thm Rep_MT2
thm module_type_environment_MT2_def

declare[[show_consts]]

lemma 
  fixes n::nat and M::"'mt::module_type"
  assumes inst: "module_type_instantiation TYPE('mt) TYPE('mtc::module_type_closed)"
(*  assumes "length (module_type_procs M) > n" *)
  shows "mk_procedure_typed (subst_proc [] (module_type_procs
         (module_type_construct (map (subst_proc procs) (module_type_procs M)) :: 'mtc)!n)) =
    mk_procedure_typed (subst_proc procs (module_type_procs M!n))"
proof -
  note mt_procT_same = inst[unfolded module_type_instantiation_def, THEN conjunct2, symmetric]
  have pt_of: "\<And>p. p\<in>set (module_type_procs M) \<Longrightarrow> proctype_of (subst_proc procs p) = proctype_of p"
    sorry
  have "module_type_procs (module_type_construct (map (subst_proc procs) (module_type_procs M)) :: 'mtc)
      = map (subst_proc procs) (module_type_procs M)"
      apply (subst module_type_construct_inverse)
      (* Goal 1 *)
      unfolding mt_procT_same module_type_procs1[of M, symmetric]
      using pt_of apply auto[1]
      (* Goal 2 *)
      unfolding closed_module_type_empty
  let ?inst = "Abs_MT_inst (map (subst_proc procs) (module_type_procs M))"
  have len: "length (module_type_procs ?inst) > n" sorry
  have subst: "subst_proc [] (module_type_procs ?inst!n) = module_type_procs ?inst!n"
    apply (subst subst_proc_empty) 
    apply (rule module_type_procs_welltyped[where m="Abs_MT_inst (map (subst_proc procs) (module_type_procs M))", unfolded closed_module_type_empty])
    using len by auto
  show ?thesis
    unfolding subst apply (subst Abs_MT_inst_inverse)
    unfolding module_type_rep_set_def apply auto
    
    thm Abs_MT2_inverse
    apply (subst)


(* TODO: *)
lemma "MT2_instantiated.b (MT2.INST MT2 MT) = MT2.b MT2 MT"
  unfolding MT2_instantiated.b_def MT2.INST_def MT2.b_def
  apply (subst subst_proc_empty)
  unfolding module_type_procs_MT2_def module_type_procs_MT2_instantiated_def
  apply (subst Abs_MT2_instantiated_inverse)
  apply (rule tmp1) using Rep_MT2 apply simp
  using Rep_MT2 unfolding module_type_rep_set_def 

ML {* !Modules.last_defined_module_type |> the |> (fn Modules.ModTypeInfo x => x)
  |> #getters |> hd |> #thm |> rep_thm
*}

typ MT2_instantiated

setup {*
fn thy => thy |> snd o
Modules.define_module_type {
  name = @{binding MT3},
  procs = [{name = @{binding x}, typ = @{typ "(bool*unit,string)procedure"}},
           {name = @{binding y}, typ = @{typ "(string*unit,string)procedure"}}],
  arguments = [{name = @{binding M}, typ = @{typ "MT"}},
               {name = @{binding M2}, typ = @{typ "MT2"}}] 
  };
*}

thm Abs_MT3_inverse
thm MT3.x_def
thm MT3.INST_def

