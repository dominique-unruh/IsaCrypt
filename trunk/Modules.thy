theory Modules
imports Lang_Typed TermX_Antiquot
begin

datatype procedure_type_open = ProcTypeOpen "procedure_type_open list" "procedure_type"


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
| wt_ProcRef: "nth_opt E i = Some(ProcTypeOpen pi_envT pi_t) \<Longrightarrow> 
   length pi_envT = length env \<Longrightarrow>
   list_all2 (\<lambda>T p. case T of ProcTypeOpen _ T \<Rightarrow> proctype_of p = T) pi_envT env \<Longrightarrow>
   list_all2 (\<lambda>T p. (\<lambda>e. well_typed_proc'' e p) (case T of ProcTypeOpen e _ \<Rightarrow> e)) pi_envT env  \<Longrightarrow>
   pi_t = \<lparr> pt_argtypes=argtypes, pt_returntype=returntype \<rparr> \<Longrightarrow>
   well_typed_proc'' E (ProcRef i env argtypes returntype)"
| wt_Proc: "well_typed'' E body \<Longrightarrow>
   list_all (\<lambda>v. \<not> vu_global v) pargs \<Longrightarrow>
   distinct pargs \<Longrightarrow>
   well_typed_proc'' E (Proc body pargs ret)"

thm well_typed''_well_typed_proc''.inducts
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

function (domintros,sequential) subst_proc_in_prog :: "procedure_rep list \<Rightarrow> program_rep \<Rightarrow> program_rep" 
and subst_proc :: "procedure_rep list \<Rightarrow> procedure_rep \<Rightarrow> procedure_rep" where
  "subst_proc_in_prog env Skip = Skip"
| "subst_proc_in_prog env (Seq c1 c2) = Seq (subst_proc_in_prog env c1) (subst_proc_in_prog env c2)"
| "subst_proc env (Proc body args ret) = Proc (subst_proc_in_prog env body) args ret"
| "subst_proc env (ProcRef i env' argsT retT)
    = subst_proc (map (subst_proc env) env') (env!i)"
by pat_completeness auto

definition "module_type_rep_set env proctypes \<equiv>
{procs. map proctype_of procs = proctypes \<and> (\<forall>p\<in>set procs. well_typed_proc'' env p)}"
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
  assumes module_type_procs_welltyped: "p\<in>set (module_type_procs m) \<Longrightarrow> well_typed_proc'' (module_type_environment TYPE('a)) p"
  assumes module_type_procs_type: "map proctype_of (module_type_procs m) = module_type_proc_types TYPE('a)"
  assumes module_type_construct_inverse: 
      "map proctype_of procs = module_type_proc_types TYPE('a)
      \<Longrightarrow> \<forall>p\<in>set procs. well_typed_proc'' (module_type_environment TYPE('a)) p
      \<Longrightarrow> module_type_procs (module_type_construct procs) = procs"
  assumes module_type_procs_inverse: "module_type_construct (module_type_procs m) = m"
  assumes module_type_procs1: "map proctype_of (module_type_procs m) = module_type_proc_types TYPE('a)"
  assumes module_type_procs2: "p\<in>set (module_type_procs m) \<Longrightarrow> well_typed_proc'' (module_type_environment TYPE('a)) p"

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

(* TODO move *)
lemma subst_proc_empty:
  assumes "well_typed_proc'' [] p"
  shows "subst_proc [] p = p"
  sorry

(* TODO move *)
lemma proctype_of_mk_procedure_untyped [simp]:
  fixes p :: "('a::procargs,'b::prog_type)procedure"
  shows "proctype_of (mk_procedure_untyped p) = procedure_type TYPE(('a::procargs,'b::prog_type)procedure)"
  sorry

(* TODO move *)
lemma well_typed''_mk_procedure_untyped [simp]:
  fixes p :: "('a::procargs,'b::prog_type)procedure"
  shows "well_typed_proc'' [] (mk_procedure_untyped p)"
  sorry

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

abbreviation "subst_proc_in_prog_dom procs pg == subst_proc_in_prog_subst_proc_dom(Inl(procs,pg))"
abbreviation "subst_proc_dom procs pc == subst_proc_in_prog_subst_proc_dom(Inr(procs,pc))"

thm subst_proc_in_prog_subst_proc.pinduct
lemma subst_proc_dom:
  defines "match \<equiv> list_all2 (\<lambda>T p. case T of ProcTypeOpen e _ \<Rightarrow> well_typed_proc'' e p)"
  assumes "match procsT procs"
  shows "well_typed'' procsT pg  \<Longrightarrow> subst_proc_in_prog_dom procs pg" (is "?t1\<Longrightarrow>?t2")
    and "well_typed_proc'' procsT pc \<Longrightarrow> subst_proc_dom procs pc" (is "?t4\<Longrightarrow>?t5")
proof -
  have thesis: "(well_typed'' procsT pg \<longrightarrow> (\<forall>procs. match procsT procs
                \<longrightarrow> subst_proc_in_prog_dom procs pg)) \<and>
        (well_typed_proc'' procsT pc \<longrightarrow> (\<forall>procs.  match procsT procs
                \<longrightarrow> subst_proc_dom procs pc))"
  proof (induct rule: well_typed''_well_typed_proc''.induct)
  case wt_Seq thus ?case by (auto, subst subst_proc_in_prog_subst_proc.domintros, auto) next
  case wt_Assign thus ?case by (auto, subst subst_proc_in_prog_subst_proc.domintros, auto) next
  case wt_While thus ?case by (auto, subst subst_proc_in_prog_subst_proc.domintros, auto) next
  case wt_Sample thus ?case by (auto, subst subst_proc_in_prog_subst_proc.domintros, auto) next
  case wt_Skip thus ?case by (auto, subst subst_proc_in_prog_subst_proc.domintros, auto) next
  case wt_IfTE thus ?case by (auto, subst subst_proc_in_prog_subst_proc.domintros, auto) next
  case wt_CallProc thus ?case by (auto, subst subst_proc_in_prog_subst_proc.domintros, auto) next
  case wt_Proc thus ?case by (auto, subst subst_proc_in_prog_subst_proc.domintros, auto) next
  case (wt_ProcRef E i pi_envT pi_t env argtypes returntype) note case_assms = this
    hence Ei: "nth_opt (E\<Colon>procedure_type_open list) (i\<Colon>nat) =
          Some (ProcTypeOpen (pi_envT\<Colon>procedure_type_open list) (pi_t\<Colon>procedure_type))" 
      and length: "length (pi_envT\<Colon>procedure_type_open list) = length (env\<Colon>procedure_rep list)"
      and "list_all2 (\<lambda>T p. case T of ProcTypeOpen x T \<Rightarrow> proctype_of p = T) pi_envT env"
     and wt_env: "list_all2 (\<lambda>T p. well_typed_proc'' (case T of ProcTypeOpen e x \<Rightarrow> e) p \<and>
         (\<forall>procs. match (case T of ProcTypeOpen e x \<Rightarrow> e) procs \<longrightarrow>
             subst_proc_dom procs p)) pi_envT env"
    and "pi_t = \<lparr>pt_argtypes = argtypes, pt_returntype = returntype\<rparr>"
    by simp_all
    show ?case
    proof (rule,rule)
      fix procs assume "match E procs"
      {fix p assume "p\<in>set env"
        then obtain j where "p=nth env j" and "j<length env"
          by (metis in_set_conv_nth)
        def T=="nth pi_envT j"
        have "well_typed_proc'' (case T of ProcTypeOpen e x \<Rightarrow> e) p \<and>
         (\<forall>procs. match (case T of ProcTypeOpen e x \<Rightarrow> e) procs \<longrightarrow>
             subst_proc_dom procs p)"
        have "subst_proc_dom procs p"
          
        sorry}
      note x_dom = this
      show "subst_proc_dom procs (ProcRef i env argtypes returntype)"
        apply (subst subst_proc_in_prog_subst_proc.domintros)
        apply (fact x_dom)
        using wt_env length by blast
        apply (auto simp: case_assms)
    
    sorry
  qed
  with assms show "?t1\<Longrightarrow>?t2" and "?t4\<Longrightarrow>?t5" by auto
qed

(*
\<forall>p\<in>set env. subst_proc_dom procs p

| "nth_opt E i = Some(ProcTypeOpen pi_envT pi_t) \<Longrightarrow> 
   length pi_envT = length env \<Longrightarrow>
   list_all2 (\<lambda>T p. case T of ProcTypeOpen _ T \<Rightarrow> proctype_of p = T) pi_envT env \<Longrightarrow>
   list_all2 (\<lambda>T p. (\<lambda>e. well_typed_proc'' e p) (case T of ProcTypeOpen e _ \<Rightarrow> e)) pi_envT env  \<Longrightarrow>
   pi_t = \<lparr> pt_argtypes=argtypes, pt_returntype=returntype \<rparr> \<Longrightarrow>
   well_typed_proc'' E (ProcRef i env argtypes returntype)"

| "subst_proc env (ProcRef i env' argsT retT)
    = subst_proc (map (subst_proc env) env') (env!i)"
*)

apply ((subst subst_proc_in_prog_subst_proc.domintros, auto)[1])
apply ((subst subst_proc_in_prog_subst_proc.domintros, auto)[1])
apply ((subst subst_proc_in_prog_subst_proc.domintros, auto)[1])
apply ((subst subst_proc_in_prog_subst_proc.domintros, auto)[1])
apply ((subst subst_proc_in_prog_subst_proc.domintros, auto)[1])

apply ((subst subst_proc_in_prog_subst_proc.domintros, auto)[1])

apply ((subst subst_proc_in_prog_subst_proc.domintros, auto)[1])
apply (rule c1,simp_all)[1]
apply (fact c2)
by ((subst subst_proc_in_prog_subst_proc.domintros, auto)[1])+
  thus "well_typed'' procsT pg \<Longrightarrow> subst_proc_in_prog_dom procs pg"
    and "well_typed_proc'' procsT pc \<Longrightarrow> subst_proc_dom procs pc" by auto
qed

lemma proctype_of_subst_proc:
  assumes wt: "well_typed_proc'' procsT p"
  shows "proctype_of (subst_proc procs m) = proctype_of p"
proof -
  show 
"proctype_of (subst_proc procs m) = proctype_of p"
thm well_typed''_well_typed_proc''.induct
  using wt apply (induct p rule:well_typed''_well_typed_proc''.induct)
sorry

lemma welltyped_subst_proc:
  assumes "welltyped_proc'' (ProcTypeOpen (module_type_environment MT)) p"
  shows "welltyped_proc'' [] (subst_proc procs m)"
sorry
*)

definition "MT2_INST == \<lambda>MT2::MT2. \<lambda>MT::MT.
  Abs_MT2_instantiated (map (subst_proc (module_type_procs MT)) (module_type_procs MT2))"
lemma "MT2_instantiated.b (MT2_INST MT2 MT) = MT2.b MT2 MT"
  unfolding MT2_INST_def MT2_instantiated.b_def module_type_procs_MT2_instantiated_def
  apply (subst Abs_MT2_instantiated_inverse)
  unfolding module_type_rep_set_def module_type_procs_MT2_def
  apply simp 
  using Rep_MT2
  unfolding module_type_rep_set_def module_type_procs_MT2_def
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

