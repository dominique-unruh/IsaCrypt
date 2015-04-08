theory Modules
imports Lang_Typed TermX_Antiquot
begin

(*datatype procedure_type_open = ProcTypeOpen "procedure_type_open list" "procedure_type"*)

fun nth_opt :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "nth_opt (x#xs) 0 = Some x"
| "nth_opt (x#xs) (Suc n) = nth_opt xs n"
| "nth_opt [] _ = None"

lemma list_all2_mono' [mono]: "A \<le> B \<Longrightarrow> list_all2 A \<le> list_all2 B"
  apply auto unfolding list_all2_iff by auto
ML {* @{term "(case T of ProcTypeOpen e T \<Rightarrow> well_typed_proc'' e p)"} *}

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
| subst_proc_ProcRef: "subst_proc insts (ProcRef i T) =
    (if i<length insts then insts!i
    else ProcRef (i-length insts) T)"
| subst_proc_ProcInst: "subst_proc insts (ProcInst inst p) = subst_proc ((subst_proc insts inst)#insts) p"
print_theorems

inductive well_typed'' :: "procedure_type_open list \<Rightarrow> program_rep \<Rightarrow> bool"
and well_typed_proc'' :: "procedure_type_open \<Rightarrow> procedure_rep \<Rightarrow> bool" where
  wt_Seq: "well_typed'' E p1 \<and> well_typed'' E p2 \<Longrightarrow> well_typed'' E (Seq p1 p2)"
| wt_Assign: "eu_type e = vu_type v \<Longrightarrow> well_typed'' E (Assign v e)"
| wt_Sample: "ed_type e = vu_type v \<Longrightarrow> well_typed'' E (Sample v e)"
| wt_Skip: "well_typed'' E Skip"
| wt_While: "eu_type e = bool_type \<Longrightarrow> well_typed'' E p \<Longrightarrow> well_typed'' E (While e p)"
| wt_IfTE: "eu_type e = bool_type \<Longrightarrow> well_typed'' E thn \<Longrightarrow>  well_typed'' E els \<Longrightarrow> well_typed'' E (IfTE e thn els)"
| wt_CallProc: "vu_type v = pt_returntype T \<Longrightarrow>
   list_all2 (\<lambda>e T. eu_type e = T) args (pt_argtypes T) \<Longrightarrow>
   well_typed_proc'' (ProcTypeOpen E T) prc \<Longrightarrow>
   well_typed'' E (CallProc v prc args)"
| wt_Proc: "well_typed'' E body \<Longrightarrow>
   list_all (\<lambda>v. \<not> vu_global v) pargs \<Longrightarrow>
   eu_type ret = pt_returntype T \<Longrightarrow>
   list_all2 (\<lambda>e T. vu_type e = T) pargs (pt_argtypes T) \<Longrightarrow>
   distinct pargs \<Longrightarrow>
   well_typed_proc'' (ProcTypeOpen E T) (Proc body pargs ret)"
| wt_ProcRef: "nth_opt E i = Some (ProcTypeOpen envT T) \<Longrightarrow> 
  well_typed_proc'' (ProcTypeOpen E T) (ProcRef i (ProcTypeOpen envT T))" (* TODO check *)
| wt_ProcInst: "
  well_typed_proc'' (ProcTypeOpen E instT) inst \<Longrightarrow>
  well_typed_proc'' (ProcTypeOpen (ProcTypeOpen E instT#E') T) prc \<Longrightarrow>
  well_typed_proc'' (ProcTypeOpen E' T) (ProcInst inst prc)"




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

definition "module_type_rep_set env proctypes \<equiv> {procs. list_all2 (\<lambda>T p. well_typed_proc'' (ProcTypeOpen env T) p) proctypes procs}"
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
          (\<lambda>T p. well_typed_proc'' (ProcTypeOpen (module_type_environment TYPE('a)) T) p)
          (module_type_proc_types TYPE('a)) (module_type_procs m)"
  assumes module_type_construct_inverse: 
      "list_all2 
          (\<lambda>T p. well_typed_proc'' (ProcTypeOpen (module_type_environment TYPE('a)) T) p)
          (module_type_proc_types TYPE('a)) procs
      \<Longrightarrow> module_type_procs (module_type_construct procs) = procs"
  assumes module_type_procs_inverse: "module_type_construct (module_type_procs m) = m"

class module_type_closed = module_type +
  assumes closed_module_type_empty: "module_type_environment TYPE('a) = []"

definition "module_type_proc_types_open MT \<equiv> 
  map (ProcTypeOpen (module_type_environment MT)) (module_type_proc_types MT)"

definition "module_type_instantiation (_::'mt::module_type itself) (_::'mtc::module_type_closed itself)
  == module_type_proc_names TYPE('mt) = module_type_proc_names TYPE('mtc)
   \<and> module_type_proc_types TYPE('mt) = module_type_proc_types TYPE('mtc)" 


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

