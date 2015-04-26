theory Lang_Typed
imports Procedures
begin

subsection {* Types *}
  
definition "Type (_::('a::prog_type) itself) 
    = Abs_type \<lparr> tr_domain=range (embedding::'a\<Rightarrow>val),
                 tr_default=embedding (default::'a) \<rparr>";

lemma bool_type: "bool_type = Type TYPE(bool)"
  unfolding bool_type_def Type_def ..

lemma embedding_Type: "embedding (x::'a::prog_type) \<in> t_domain (Type TYPE('a))"
  unfolding Type_def t_domain_def
  by (subst Abs_type_inverse, auto)
lemma embedding_Type_range: "range (embedding::'a\<Rightarrow>val) = t_domain (Type TYPE('a::prog_type))"
  unfolding Type_def t_domain_def
  by (subst Abs_type_inverse, auto)

subsection {* Variables *}

datatype ('a::prog_type) variable = Variable variable_name | LVariable variable_name
definition mk_variable_untyped :: "('a::prog_type) variable \<Rightarrow> variable_untyped" where
  "mk_variable_untyped (v::('a::prog_type)variable) = 
    (case v of Variable n \<Rightarrow> \<lparr> vu_name=n, vu_type=Type TYPE('a), vu_global=True \<rparr>
            | LVariable n \<Rightarrow> \<lparr> vu_name=n, vu_type=Type TYPE('a), vu_global=False \<rparr>)"
lemma mk_variable_untyped_type [simp]: "vu_type (mk_variable_untyped (v::'a variable)) = Type TYPE('a::prog_type)"
  unfolding mk_variable_untyped_def apply (cases v) by auto
definition var_eq :: "'a::prog_type variable \<Rightarrow> 'b::prog_type variable \<Rightarrow> bool" where
  "var_eq v1 v2 = (mk_variable_untyped v1 = mk_variable_untyped v2)" 
lemma var_eq_same [simp]: "var_eq v v"
  unfolding var_eq_def by simp
lemma var_eq_notsame_gg [simp]: "v\<noteq>w \<Longrightarrow> \<not> var_eq (Variable v) (Variable w)"
  unfolding var_eq_def mk_variable_untyped_def by simp
lemma var_eq_notsame_ll [simp]: "v\<noteq>w \<Longrightarrow> \<not> var_eq (LVariable v) (LVariable w)"
  unfolding var_eq_def mk_variable_untyped_def by simp
lemma var_eq_notsame_gl [simp]: "\<not> var_eq (Variable v) (LVariable w)"
  unfolding var_eq_def mk_variable_untyped_def by simp
lemma var_eq_notsame_lg [simp]: "\<not> var_eq (LVariable v) (Variable w)"
  unfolding var_eq_def mk_variable_untyped_def by simp

subsection {* Memories *}

definition "memory_lookup m (v::'a variable) :: ('a::prog_type) == inv embedding (memory_lookup_untyped m (mk_variable_untyped v))"
definition "memory_update m (v::'a variable) (a::'a::prog_type) =
  memory_update_untyped m (mk_variable_untyped v) (embedding a)"
lemma memory_lookup_update_same [simp]: "memory_lookup (memory_update m v a) v = a"
  unfolding memory_lookup_def memory_update_def
  apply (subst memory_lookup_update_same_untyped)
  close (metis embedding_Type mk_variable_untyped_type)
  by (metis embedding_inv f_inv_into_f rangeI)
lemma memory_lookup_update_same': "var_eq v w \<Longrightarrow> (memory_lookup (memory_update m v a) w == a)"
  unfolding memory_lookup_def memory_update_def
  by (smt2 memory_lookup_def memory_lookup_update_same memory_update_def var_eq_def)
lemma memory_lookup_update_notsame [simp]: 
  "\<not>var_eq v w \<Longrightarrow> memory_lookup (memory_update m v a) w == memory_lookup m w"
  unfolding var_eq_def memory_lookup_def memory_update_def
  by (simp add: memory_lookup_update_notsame_untyped)  
  
subsection {* Expressions *}

record 'a expression_rep =
  er_fun :: "memory \<Rightarrow> 'a"
  er_vars :: "variable_untyped list"
typedef 'a expression = "{(e::'a expression_rep).
  (\<forall>m1 m2. (\<forall>v\<in>set (er_vars e). memory_lookup_untyped m1 v = memory_lookup_untyped m2 v) \<longrightarrow> er_fun e m1 = er_fun e m2)}";
  by (rule exI[of _ "\<lparr> er_fun=(\<lambda>m. undefined),
                       er_vars=[] \<rparr>"], simp);
definition "e_fun e == er_fun (Rep_expression e)"
definition "e_vars e == er_vars (Rep_expression e)"
definition "mk_expression_untyped (e::('a::prog_type)expression) =
  Abs_expression_untyped \<lparr> eur_fun=\<lambda>m. embedding (e_fun e m),
                           eur_type=Type TYPE('a),
                           eur_vars=e_vars e \<rparr>"
definition "mk_expression_typed (e::expression_untyped) = 
  Abs_expression \<lparr> er_fun=\<lambda>m. inv embedding (eu_fun e m),
                   er_vars=eu_vars e \<rparr>"
lemma mk_expression_typed_inverse:
  assumes "eu_type e=Type TYPE('a)"
  shows "mk_expression_untyped (mk_expression_typed e :: 'a::prog_type expression) = e"
proof (rule trans[OF _ Rep_expression_untyped_inverse], cases "Rep_expression_untyped e")
  fix f t v assume e_parts: "Rep_expression_untyped e = \<lparr>eur_fun=f, eur_type=t, eur_vars=v\<rparr>"
  have f_t: "\<And>m. f m \<in> t_domain t"
    by (metis (erased, lifting) Rep_expression_untyped e_parts expression_untyped_rep.select_convs(1) expression_untyped_rep.select_convs(2) mem_Collect_eq)
  have t: "t=Type TYPE('a)"
    by (metis assms e_parts eu_type_def expression_untyped_rep.select_convs(2)) 
  have f_touches: "\<And>m1 m2. (\<forall>v\<in>set v. 
    memory_lookup_untyped m1 v = memory_lookup_untyped m2 v) \<longrightarrow> f m1 = f m2"
    using Rep_expression_untyped[of e] unfolding e_parts by auto
  have rep_abs: "Rep_expression (Abs_expression \<lparr>er_fun = \<lambda>m. inv embedding (f m), er_vars = v\<rparr>)
              = \<lparr>er_fun = \<lambda>m. inv embedding (f m), er_vars = v\<rparr>"
    by (subst Abs_expression_inverse, auto, metis f_touches)
  have inv: "\<And>m. embedding (inv embedding (f m)::'a) = f m"
    apply (subst f_inv_into_f[where f=embedding], auto)
    using f_t unfolding t embedding_Type_range .
  have h1: "mk_expression_untyped (Abs_expression \<lparr>er_fun = \<lambda>m. inv embedding (f m), er_vars = v\<rparr> :: 'a expression) =
    Abs_expression_untyped \<lparr>eur_fun = f, eur_type = t, eur_vars = v\<rparr>"
    unfolding mk_expression_untyped_def 
    apply (subst Abs_expression_untyped_inject)
    unfolding e_fun_def e_vars_def
    apply (auto simp: embedding_Type)
    close (smt2 Rep_expression mem_Collect_eq)
    close (fact f_t)
    close (metis f_touches)
    unfolding rep_abs apply (auto simp: t)
    by (simp add: inv)

  show "mk_expression_untyped (mk_expression_typed e::'a expression) =
       Abs_expression_untyped (Rep_expression_untyped e)"
       unfolding e_parts
       apply (subst mk_expression_typed_def)
       unfolding eu_fun_def eu_vars_def e_parts apply simp
       using h1 .
qed

lemma mk_expression_untyped_fun [simp]: "eu_fun (mk_expression_untyped (e::'a::prog_type expression)) m = embedding (e_fun e m)"
  unfolding mk_expression_untyped_def eu_fun_def
  apply (subst Abs_expression_untyped_inverse, auto simp: embedding_Type)
  by (smt2 Rep_expression e_fun_def e_vars_def mem_Collect_eq)
lemma mk_expression_untyped_type [simp]: "eu_type (mk_expression_untyped (e::'a::prog_type expression)) = Type TYPE('a)"
  unfolding mk_expression_untyped_def eu_type_def
  apply (subst Abs_expression_untyped_inverse, auto simp: embedding_Type)
  by (smt2 Rep_expression e_fun_def e_vars_def mem_Collect_eq)  
lemma mk_expression_untyped_vars [simp]: "eu_vars (mk_expression_untyped (e::'a::prog_type expression)) = e_vars e"
  unfolding mk_expression_untyped_def eu_vars_def
  apply (subst Abs_expression_untyped_inverse, auto simp: embedding_Type)
  by (smt2 Rep_expression e_fun_def e_vars_def mem_Collect_eq)  
lemma e_fun_bool_untyped: "e_fun (e::bool expression) m = (eu_fun (mk_expression_untyped e) m = embedding True)"
  by (metis (poly_guards_query) embedding_inv mk_expression_untyped_fun)

definition "mk_expression_distr (e::('a::prog_type)distr expression) =
  Abs_expression_distr \<lparr> edr_fun=\<lambda>m. apply_to_distr embedding (e_fun e m),
                         edr_type=Type TYPE('a),
                         edr_vars=e_vars e \<rparr>"

lemma mk_expression_distr_fun [simp]: "ed_fun (mk_expression_distr (e::'a::prog_type distr expression)) m = apply_to_distr embedding (e_fun e m)"
  unfolding mk_expression_distr_def ed_fun_def
  apply (subst Abs_expression_distr_inverse, auto simp: embedding_Type)
  unfolding e_fun_def e_vars_def 
  using Rep_expression[of e] by (auto, metis)

lemma mk_expression_distr_type [simp]: "ed_type (mk_expression_distr (e::'a::prog_type distr expression)) = Type TYPE('a)"
  unfolding mk_expression_distr_def ed_type_def
  apply (subst Abs_expression_distr_inverse, auto simp: embedding_Type)
  unfolding e_fun_def e_vars_def 
  using Rep_expression[of e] by (auto, metis)


definition const_expression :: "'a \<Rightarrow> 'a expression" where
  "const_expression x = Abs_expression \<lparr> er_fun=\<lambda>m. x, er_vars=[] \<rparr>";
lemma e_fun_const_expression [simp]: "e_fun (const_expression a) = (\<lambda>m. a)"
  unfolding const_expression_def e_fun_def
  by (subst Abs_expression_inverse, auto)

definition apply_expression :: "('a\<Rightarrow>'b)expression \<Rightarrow> ('a::prog_type) variable \<Rightarrow> 'b expression" where
"apply_expression e v = Abs_expression
  \<lparr> er_fun=\<lambda>m. (e_fun e m) (memory_lookup m v),
    er_vars=mk_variable_untyped v#e_vars e \<rparr>";
lemma e_fun_apply_expression [simp]: "e_fun (apply_expression e v) = (\<lambda>m. (e_fun e m) (memory_lookup m v))"
  unfolding apply_expression_def e_fun_def e_vars_def memory_lookup_def
  apply (subst Abs_expression_inverse, auto)
  proof - (* Autogenerated by sledgehammer *)
    fix m1 :: memory and m2 :: memory
    assume "memory_lookup_untyped m1 (mk_variable_untyped v) = memory_lookup_untyped m2 (mk_variable_untyped v)"
    assume a1: "\<forall>v\<in>set (er_vars (Rep_expression e)). memory_lookup_untyped m1 v = memory_lookup_untyped m2 v"
    have "\<And>b_x. \<forall>R Ra. (\<forall>Rb. Rb \<in> set (er_vars (Rep_expression b_x)) \<longrightarrow> memory_lookup_untyped R Rb = memory_lookup_untyped Ra Rb) \<longrightarrow> (er_fun (Rep_expression b_x) R\<Colon>'b \<Rightarrow> 'a) = er_fun (Rep_expression b_x) Ra" using Rep_expression by auto
    thus "er_fun (Rep_expression e) m1 (inv embedding (memory_lookup_untyped m2 (mk_variable_untyped v))) 
        = er_fun (Rep_expression e) m2 (inv embedding (memory_lookup_untyped m2 (mk_variable_untyped v)))" using a1 by metis
  qed
definition var_expression :: "('a::prog_type) variable \<Rightarrow> 'a expression" where
"var_expression v = Abs_expression
  \<lparr> er_fun=\<lambda>m. memory_lookup m v,
    er_vars=[mk_variable_untyped v] \<rparr>";
lemma e_fun_var_expression [simp]: "e_fun (var_expression v) = (\<lambda>m. memory_lookup m v)"
  unfolding e_fun_def var_expression_def memory_lookup_def
  by (subst Abs_expression_inverse, auto)

subsection {* Procedures *}

class procargs =
  fixes procargs_len :: "'a itself \<Rightarrow> nat"
  fixes procargtypes :: "'a itself \<Rightarrow> type list"
  assumes procargtypes_len: "length (procargtypes TYPE('a)) = procargs_len TYPE('a)"

definition "procargs (_::'a::procargs itself) == {vs. map eu_type vs = procargtypes TYPE('a)}"
lemma procargs_not_empty: "procargs (TYPE(_)) \<noteq> {}"
  unfolding procargs_def apply auto
  by (metis ex_map_conv expression_type_inhabited)

lemma procargs_len: "\<forall>x\<in>procargs TYPE('a::procargs). length x = procargs_len TYPE('a)"
  unfolding procargs_def by (metis (full_types) length_map procargtypes_len mem_Collect_eq) 

lemma procargs_typematch'': "\<forall>vs\<in>procargs TYPE('a::procargs). map eu_type vs = procargtypes TYPE('a)"
  unfolding procargs_def by auto

definition procargvars :: "'a::procargs itself \<Rightarrow> variable_untyped list set" where
  "procargvars _ = {vs. distinct vs \<and> list_all2 (\<lambda>v t. vu_type v = t) vs (procargtypes TYPE('a)) \<and> 
                    (\<forall>v\<in>set vs. \<not> vu_global v)}"
lemma procargvars_inhabited: "procargvars TYPE('a::procargs) \<noteq> {}" 
  unfolding procargvars_def apply auto
  sorry
lemma procargvars_local: "\<forall>l\<in>procargvars TYPE('a::procargs). \<forall>v\<in>set l. \<not> vu_global v"
  unfolding procargvars_def by auto
lemma procargvars_distinct: "\<forall>vs\<in>procargvars TYPE('a::procargs). distinct vs"
  unfolding procargvars_def by auto
lemma procargs_typematch: "\<forall>es\<in>procargs TYPE('a::procargs). \<forall>vs\<in>procargvars TYPE('a). 
     map vu_type vs = map eu_type es"
  sorry

instantiation unit :: procargs begin
definition "procargtypes (_::unit itself) = []"
definition "procargs_len (_::unit itself) = 0"
instance apply intro_classes 
  unfolding procargs_len_unit_def 
            procargtypes_unit_def by auto
end

instantiation prod :: (prog_type,procargs) procargs begin
definition "procargs_len (_::('a::prog_type*'b) itself) = Suc (procargs_len TYPE('b))"
definition "procargtypes (_::('a::prog_type*'b) itself) = Type TYPE('a) # procargtypes TYPE('b)"
instance apply intro_classes 
  unfolding procargs_len_prod_def 
            mk_variable_untyped_def procargtypes_prod_def
  apply (auto simp: procargs_not_empty procargs_len)
  by (metis procargtypes_len)
end

typedef ('a::procargs) procargs = "procargs TYPE('a)" using procargs_not_empty by auto
abbreviation "mk_procargs_untyped == Rep_procargs"
typedef ('a::procargs) procargvars = "procargvars TYPE('a)" using procargvars_inhabited by auto
abbreviation "mk_procargvars_untyped == Rep_procargvars"
(* TODO: procargvars should be all disjoint *)

record ('a::procargs,'b) procedure = 
  p_body :: program
  p_args :: "'a procargvars"
  p_return :: "'b expression"

definition "mk_procedure_untyped proc = 
  Proc (mk_program_untyped (p_body proc)) (Rep_procargvars (p_args proc)) (mk_expression_untyped (p_return proc))"

fun mk_procedure_typed :: "procedure_rep \<Rightarrow> ('a::procargs, 'b::prog_type, 'c) procedure_ext"  where
 "mk_procedure_typed (Proc body args return) = 
    \<lparr> p_body=Abs_program body, p_args=Abs_procargvars args, p_return=mk_expression_typed return, \<dots> = undefined\<rparr>"
| "mk_procedure_typed _ = undefined"

lemma mk_procedure_typed_inverse:
  fixes body args return
  assumes "well_typed body"
  assumes "args \<in> procargvars TYPE('a)"
  assumes "eu_type return = Type TYPE('b)"
  defines "p == Proc body args return"
  shows "mk_procedure_untyped (mk_procedure_typed p :: ('a::procargs,'b::prog_type,'c)procedure_ext) = p"
  unfolding mk_procedure_untyped_def p_def apply auto
  apply (subst Abs_program_inverse, auto simp: assms)
  apply (subst Abs_procargvars_inverse, auto simp: assms)
  apply (subst mk_expression_typed_inverse, auto simp: assms)
done

definition "procedure_type (_::('a::procargs,'b::prog_type,'c) procedure_ext itself) = 
  \<lparr> pt_argtypes=procargtypes TYPE('a), pt_returntype=Type TYPE('b) \<rparr>"

lemma mk_procedure_untyped:
  fixes p0::"('a::procargs,'b::prog_type,'c)procedure_ext"
  defines "p == mk_procedure_untyped p0"
  shows "well_typed_proc p" and "proctype_of p = procedure_type TYPE(('a,'b,'c)procedure_ext)"
SORRY


definition procargs_empty :: "unit procargs" where
  "procargs_empty = Abs_procargs []"
definition procargs_add :: "('a::prog_type) expression \<Rightarrow> ('b::procargs) procargs \<Rightarrow> ('a*'b) procargs" where
  "procargs_add e es = Abs_procargs (mk_expression_untyped e#Rep_procargs es)"
definition procargvars_empty :: "unit procargvars" where
  "procargvars_empty = Abs_procargvars []"
definition procargvars_add :: "('a::prog_type) variable \<Rightarrow> ('b::procargs) procargvars \<Rightarrow> ('a*'b) procargvars" where
  "procargvars_add v vs = Abs_procargvars (mk_variable_untyped v#Rep_procargvars vs)"


lemma procedure_type_procargvars:
  assumes procT: "proctype_of (Proc body args ret) = procedure_type TYPE(('a::procargs,'b::prog_type)procedure)"
  and wt: "well_typed_proc (Proc body args ret)"
  shows "args \<in> procargvars TYPE('a)"
proof -
  from procT have t: "procargtypes TYPE('a) = map vu_type args"
    by (simp add: procedure_type_def)
  from wt have dist_glob: "distinct args \<and> (\<forall>v\<in>set args. \<not> vu_global v)"
    by (simp, metis list_all_iff)
  show "args \<in> procargvars TYPE('a)"
    unfolding procargvars_def apply (simp add: dist_glob)
    unfolding t list_all2_map2
    by (rule list_all2_refl, simp)
qed

subsection {* Procedure functors *}

class procedure_functor =
  fixes procedure_functor_type :: "'a itself \<Rightarrow> procedure_type_open"
  fixes procedure_functor_mk_untyped :: "'a \<Rightarrow> procedure_rep"
  fixes procedure_functor_mk_typed :: "procedure_rep \<Rightarrow> 'a"
  assumes procedure_functor_welltyped: "well_typed_proc'' [] (procedure_functor_mk_untyped (p::'a)) (procedure_functor_type TYPE('a))"
  assumes procedure_functor_beta_reduced: "beta_reduced (procedure_functor_mk_untyped (p::'a))"
  assumes procedure_functor_mk_typed_inverse: 
    "well_typed_proc'' [] q (procedure_functor_type TYPE('a)) \<Longrightarrow> beta_reduced q
       \<Longrightarrow> procedure_functor_mk_untyped (procedure_functor_mk_typed q) = q"
  assumes procedure_functor_mk_untyped_inverse:
    "procedure_functor_mk_typed (procedure_functor_mk_untyped p) = p"

typedef ('a::procedure_functor,'b::procedure_functor) procfun = "{p::procedure_rep.
  well_typed_proc'' [] p (ProcTFun (procedure_functor_type TYPE('a)) (procedure_functor_type TYPE('b)))
  \<and> beta_reduced p}"
  apply (rule exI[of _ "ProcAbs (procedure_functor_mk_untyped (undefined::'b))"], auto)
  apply (rule wt_ProcAbs, rule well_typed_extend, rule procedure_functor_welltyped)
  by (metis beta_reduced_def brc_ProcAbs procedure_functor_beta_reduced)

type_notation "procfun" (infixr "=proc=>" 0)

instantiation procfun :: (procedure_functor,procedure_functor) procedure_functor begin
definition "procedure_functor_type (_::('a,'b)procfun itself)
     == ProcTFun (procedure_functor_type TYPE('a)) (procedure_functor_type TYPE('b))"
definition "procedure_functor_mk_untyped == Rep_procfun"
definition "procedure_functor_mk_typed == Abs_procfun"
instance apply intro_classes 
  unfolding procedure_functor_type_procfun_def procedure_functor_mk_untyped_procfun_def
            procedure_functor_mk_typed_procfun_def
  using Rep_procfun close auto
  close (metis Rep_procfun mem_Collect_eq)
  using Rep_procfun_inverse apply auto
  by (smt2 Abs_procfun_inverse mem_Collect_eq well_typed_extend(2))
end

instantiation prod :: (procedure_functor,procedure_functor) procedure_functor begin
definition "procedure_functor_type (_::('a*'b) itself)
     == ProcTPair (procedure_functor_type TYPE('a)) (procedure_functor_type TYPE('b))"
definition "procedure_functor_mk_untyped == (\<lambda>(x,y). ProcPair (procedure_functor_mk_untyped x) (procedure_functor_mk_untyped y))"
definition "procedure_functor_mk_typed p == (case p of ProcPair x y \<Rightarrow> (procedure_functor_mk_typed x, procedure_functor_mk_typed y))"
instance apply intro_classes 
  unfolding procedure_functor_type_prod_def procedure_functor_mk_untyped_prod_def
            procedure_functor_mk_typed_prod_def
  close (auto, rule well_typed''_well_typed_proc''.intros, simp_all add: procedure_functor_welltyped)
  apply (case_tac p, clarify)
  apply (auto simp: beta_reduced_def, erule beta_reduce_proc.cases, auto)[]
    using procedure_functor_beta_reduced unfolding beta_reduced_def close auto
    using procedure_functor_beta_reduced unfolding beta_reduced_def close auto
  defer
  close (auto simp: procedure_functor_mk_untyped_inverse)[]
  apply (ind_cases "well_typed_proc'' [] q (ProcTPair a b)" for q a b, auto)
  by simp
end


(* TODO move *)
lemma well_typed_well_typed'': 
  shows "well_typed p \<Longrightarrow> well_typed'' [] p"
  apply (induction rule:well_typed.induct) close (auto simp: wt_Seq)
  close (simp add: wt_Assign) close (simp add: wt_Sample) close (simp add: wt_Skip)
  close (simp add: wt_While) close (simp add: wt_IfTE) close (simp add: wt_CallProc wt_Proc)
  by auto

(* TODO move *)
lemma well_typed_proc_well_typed_proc'':
  shows "well_typed_proc p \<Longrightarrow> well_typed_proc'' [] p (ProcTSimple (proctype_of p))"
apply (cases p, auto) apply (rule wt_Proc, auto) by (rule well_typed_well_typed'', simp)


(* TODO move *)
lemma well_typed_proc_beta_reduced: 
  shows "well_typed_proc p \<Longrightarrow> beta_reduced p"
SORRY

(* TODO move *)
lemma well_typed_proc''_well_typed:
  assumes "well_typed_proc'' [] p (ProcTSimple (proctype_of p))"
  assumes "beta_reduced p"
  shows "well_typed_proc p"
SORRY

(* TODO move *)
lemma well_typed_ProcTSimple_Proc:
  assumes "well_typed_proc'' [] p (ProcTSimple T)"
  obtains body ret args where "p = Proc body ret args"
SORRY

instantiation procedure_ext :: (procargs,prog_type,type) procedure_functor begin
definition "procedure_functor_type (_::('a,'b,'c)procedure_ext itself) == ProcTSimple (procedure_type TYPE(('a,'b,'c)procedure_ext))"
definition "procedure_functor_mk_untyped == mk_procedure_untyped"
definition "procedure_functor_mk_typed == mk_procedure_typed"
instance apply intro_classes unfolding procedure_functor_type_procedure_ext_def procedure_functor_mk_untyped_procedure_ext_def procedure_functor_mk_typed_procedure_ext_def 
  using well_typed_proc_well_typed_proc'' mk_procedure_untyped close metis
  using well_typed_proc_beta_reduced mk_procedure_untyped close auto
  apply (rule_tac p=q in well_typed_ProcTSimple_Proc) close simp
  apply (hypsubst, subst mk_procedure_typed_inverse)
  apply (subgoal_tac "well_typed_proc (Proc body ret args)")
  close simp
  
  using well_typed_proc''_well_typed mk_procedure_typed_inverse close auto
  using mk_procedure_untyped_inverse by auto
end

definition procfun_apply :: "('a::procedure_functor,'b::procedure_functor)procfun \<Rightarrow> 'a \<Rightarrow> 'b" where
   "procfun_apply f p = procedure_functor_mk_typed (apply_procedure (procedure_functor_mk_untyped f) (procedure_functor_mk_untyped p))"

subsection {* Typed programs *}

definition "label (l::string) (p::program) = p"

definition "seq p q = Abs_program (Seq (mk_program_untyped p) (mk_program_untyped q))"

lemma mk_untyped_seq: "mk_program_untyped (seq p q) = Seq (mk_program_untyped p) (mk_program_untyped q)"
  unfolding seq_def denotation_def apply (subst Abs_program_inverse) by auto

definition "skip = Abs_program Skip"

lemma mk_untyped_skip: "mk_program_untyped skip = Skip"
  unfolding skip_def denotation_def apply (subst Abs_program_inverse) by auto

definition "assign (v::('a::prog_type) variable) (e::'a expression) =
  Abs_program (Assign (mk_variable_untyped v) (mk_expression_untyped e))"

lemma mk_untyped_assign: "mk_program_untyped (assign v e) = Assign (mk_variable_untyped v) (mk_expression_untyped e)"
  unfolding assign_def denotation_def apply (subst Abs_program_inverse) by auto
  
definition "sample (v::('a::prog_type) variable) (e::'a distr expression) =
  Abs_program (Sample (mk_variable_untyped v) (mk_expression_distr e))"

lemma mk_untyped_sample: "mk_program_untyped (sample v e) = Sample (mk_variable_untyped v) (mk_expression_distr e)"
  unfolding sample_def denotation_def apply (subst Abs_program_inverse) by auto

definition ifte :: "bool expression \<Rightarrow> program \<Rightarrow> program \<Rightarrow> program" where
  "ifte e thn els = Abs_program (IfTE (mk_expression_untyped e) (mk_program_untyped thn) (mk_program_untyped els))"

lemma mk_untyped_ifte: "mk_program_untyped (ifte e thn els) =
  IfTE (mk_expression_untyped e) (mk_program_untyped thn) (mk_program_untyped els)"
  unfolding ifte_def denotation_def apply (subst Abs_program_inverse) using bool_type by auto

definition while :: "bool expression \<Rightarrow> program \<Rightarrow> program" where
  "while e p = Abs_program (While (mk_expression_untyped e) (mk_program_untyped p))"

lemma mk_untyped_while: "mk_program_untyped (while e p) =
  While (mk_expression_untyped e) (mk_program_untyped p)"
  unfolding while_def denotation_def apply (subst Abs_program_inverse) using bool_type by auto

definition callproc :: "'a::prog_type variable \<Rightarrow> ('b::procargs,'a) procedure \<Rightarrow> 'b procargs \<Rightarrow> program" where
  "callproc v proc args = Abs_program (CallProc (mk_variable_untyped v) (mk_procedure_untyped proc) (mk_procargs_untyped args))"

lemma list_all2_swap: "list_all2 P x y = list_all2 (\<lambda>x y. P y x) y x"
  by (metis list_all2_conv_all_nth)

lemma mk_untyped_callproc: "mk_program_untyped (callproc v proc args) =
  CallProc (mk_variable_untyped v) (mk_procedure_untyped proc) (mk_procargs_untyped args)"
proof -
  have swap: "\<And>x y. list_all2 (\<lambda>(x::variable_untyped) y. vu_type x = eu_type y) x y = list_all2 (\<lambda>y x. eu_type y = vu_type x) y x"
   unfolding list_all2_conv_all_nth by auto
  show ?thesis
  unfolding callproc_def denotation_def mk_procedure_untyped_def 
  apply (subst Abs_program_inverse, auto)
  close (metis Rep_procargs Rep_procargvars procargs_typematch)
  unfolding list_all_iff using Rep_procargvars procargvars_local close auto
  using Rep_procargvars procargvars_distinct by auto
qed

(*lemma denotation_seq: "denotation (seq p q) m = 
  compose_distr (denotation_untyped (mk_program_untyped q)) (denotation_untyped (mk_program_untyped p) m)" *)
lemma denotation_seq: "denotation (seq p q) m = 
  compose_distr (denotation q) (denotation p m)"
unfolding denotation_def memory_update_def mk_untyped_seq by simp

lemma denotation_skip: "denotation skip m = point_distr m"
unfolding denotation_def memory_update_def mk_untyped_skip by simp

lemma denotation_assign: "denotation (assign v e) m = point_distr (memory_update m v (e_fun e m))"
  unfolding denotation_def memory_update_def mk_untyped_assign by simp
lemma denotation_sample: "denotation (sample v e) m = apply_to_distr (memory_update m v) (e_fun e m)"
  unfolding denotation_def memory_update_def[THEN ext] mk_untyped_sample by auto

lemma denotation_ifte: "denotation (ifte e thn els) m = (if e_fun e m then denotation thn m else denotation els m)"
  unfolding denotation_def mk_untyped_ifte by simp
lemma denotation_while: "denotation (while e p) m = Abs_distr (\<lambda>m'. \<Sum>n. Rep_distr (compose_distr (\<lambda>m. if e_fun e m then 0 else point_distr m)
                                                  (while_iter n (e_fun e) (denotation p) m)) m')"
  unfolding denotation_def mk_untyped_while by simp 

lemma denotation_callproc: "denotation (callproc v proc args) m =
  apply_to_distr (restore_locals m)
     (denotation_untyped (mk_program_untyped (p_body proc))
       (init_locals (mk_procargvars_untyped (p_args proc)) (mk_procargs_untyped args) m))"
  unfolding denotation_def mk_untyped_callproc mk_procedure_untyped_def by simp

lemma denotation_seq_skip [simp]: "denotation (seq Lang_Typed.skip c) = denotation c"
  unfolding denotation_seq[THEN ext] mk_untyped_skip denotation_def by simp 

lemmas denotation_simp = denotation_seq denotation_skip denotation_assign denotation_sample denotation_ifte denotation_while denotation_callproc

(* TODO: goes in the wrong direction for nice formatting.
  We want left parenthized denotations! *)
lemma denotation_seq_assoc: "denotation (seq (seq x y) z) = denotation (seq x (seq y z))"
  unfolding denotation_seq[THEN ext] 
  unfolding compose_distr_assoc ..


subsection {* Concrete syntax for programs *}

subsubsection {* Grammar *}

nonterminal procedure_call_args_syntax
nonterminal procedure_call_args_syntax'
syntax "_procedure_call_args_none" :: procedure_call_args_syntax ("'(')")
syntax "_procedure_call_args_single" :: "'a \<Rightarrow> procedure_call_args_syntax'" ("_")
syntax "_procedure_call_args_cons" :: "'a \<Rightarrow> procedure_call_args_syntax' \<Rightarrow> procedure_call_args_syntax'" ("_,_")
syntax "" :: "procedure_call_args_syntax' \<Rightarrow> procedure_call_args_syntax" ("'(_')")

nonterminal program_syntax


syntax "_program" :: "program_syntax \<Rightarrow> term" ("PROGRAM [ _; ]")
syntax "_program" :: "program_syntax \<Rightarrow> term" ("PROGRAM [ _ ]")
syntax "_label" :: "idt \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("_: _" [10,11] 10)
syntax "_seq" :: "program_syntax \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("_;/ _" [10,11] 10)
syntax "_skip" :: "program_syntax" ("skip")
syntax "_quote" :: "program \<Rightarrow> program_syntax" ("\<guillemotleft>_\<guillemotright>" [31] 30)
syntax "_assign" :: "idt \<Rightarrow> 'a \<Rightarrow> program_syntax" (infix ":=" 30)
syntax "_sample" :: "idt \<Rightarrow> 'a \<Rightarrow> program_syntax" (infix "<-" 30)
syntax "_ifte" :: "bool \<Rightarrow> program_syntax \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("if '(_') (2_) else (2_)" [0,20] 20)
syntax "_ifthen" :: "bool \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("if '(_') (2_)" [0,20] 20)
syntax "_while" :: "bool \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("while '(_') (2_)" [0,20] 20)
syntax "_assign_quote" :: "'a variable \<Rightarrow> 'a expression \<Rightarrow> program_syntax" ("_ := \<guillemotleft>_\<guillemotright>" [31,31] 30)
syntax "_sample_quote" :: "'a variable \<Rightarrow> 'a expression \<Rightarrow> program_syntax" ("_ <- \<guillemotleft>_\<guillemotright>" [31,31] 30)
syntax "_while_quote" :: "bool expression \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("while '(\<guillemotleft>_\<guillemotright>') (2_)" [0,20] 20)
syntax "_ifte_quote" :: "bool expression \<Rightarrow> program_syntax \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("if '(\<guillemotleft>_\<guillemotright>') (2_) else _" [0,20] 20)
syntax "_ifthen_quote" :: "bool expression \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("if '(\<guillemotleft>_\<guillemotright>') (2_)" [0,20] 20)
syntax "_callproc" :: "idt \<Rightarrow> ('a,'b) procedure \<Rightarrow> procedure_call_args_syntax \<Rightarrow> program_syntax" ("_ := call _ _" 30)
(*syntax "_local_var" :: "idt \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("local _;/ _" [10,11] 10)*)
syntax "" :: "program_syntax \<Rightarrow> program_syntax" ("{ _ }")
syntax "" :: "program_syntax \<Rightarrow> program_syntax" ("'(_')")
syntax "" :: "program_syntax \<Rightarrow> program_syntax" ("'(_;')")
syntax "" :: "program_syntax \<Rightarrow> program_syntax" ("{ _; }")
syntax "_var_access" :: "'a variable \<Rightarrow> 'a" ("$_" [1000] 999)
definition program :: "program \<Rightarrow> program" where "program p = p"

subsubsection {* Translation functions *}

ML_file "lang_syntax.ML"

parse_translation {* [("_program", fn ctx => fn p => 
    Const(@{const_syntax program},dummyT) $ 
      Lang_Syntax.translate_program ctx (Unsynchronized.ref[]) (hd p))] *};

print_translation {* [(@{const_syntax program}, fn ctx => fn p => Const("_program",dummyT) $ Lang_Syntax.translate_program_back ctx (hd p))] *};

subsection {* Concrete grammar for procedures *}

nonterminal procedure_decl_args_syntax
nonterminal procedure_decl_args_syntax'
syntax "_procedure_decl_args_none" :: procedure_decl_args_syntax ("'(')")
syntax "_procedure_decl_args_single" :: "idt \<Rightarrow> procedure_decl_args_syntax'" ("_")
syntax "_procedure_decl_args_cons" :: "idt \<Rightarrow> procedure_decl_args_syntax' \<Rightarrow> procedure_decl_args_syntax'" ("_,_")
syntax "" :: "procedure_decl_args_syntax' \<Rightarrow> procedure_decl_args_syntax" ("'(_')")
syntax "_procedure_decl" :: "procedure_decl_args_syntax \<Rightarrow> program_syntax \<Rightarrow> 'b \<Rightarrow> ('a,'b) procedure" ("proc _ {_; return _}")
syntax "_procedure_decl" :: "procedure_decl_args_syntax \<Rightarrow> program_syntax \<Rightarrow> 'b \<Rightarrow> ('a,'b) procedure" ("proc _ {_; return _;}")

parse_translation {* [("_procedure_decl", fn ctx => fn [args,body,return] => 
let val known = Unsynchronized.ref[] (* TODO: add local vars *)
    fun trargs (Const("_procedure_decl_args_none",_)) = Const(@{const_name procargvars_empty},dummyT)
      | trargs (Const("_procedure_decl_args_single",_)$x) = 
          (Lang_Syntax.add_var known x; Const(@{const_name procargvars_add},dummyT) $ x $ Const(@{const_name procargvars_empty},dummyT))
      | trargs (Const("_procedure_decl_args_cons",_)$x$xs) = 
          (Lang_Syntax.add_var known x; Const(@{const_name procargvars_add},dummyT) $ x $ trargs xs)
      | trargs t = raise (TERM ("trargs",[t]))
    val args = trargs args
in
Const(@{const_name Lang_Typed.procedure.procedure_ext},dummyT) $ 
   Lang_Syntax.translate_program ctx known body $ (* p_body *)
   args $ (* p_args *)
   Lang_Syntax.translate_expression ctx known return $ (* p_return *)
   Const(@{const_name Product_Type.Unity},dummyT)
end)] *}

subsection "Support for defining typed procedure functors"

term "proc() { x:=1; return () }"

term mk_procedure_typed

definition "subst_prog1 p q = Abs_program (subst_proc_in_prog 0 (procedure_functor_mk_untyped p) q)"

term curry
consts curry_proc :: "('a \<times> 'b =proc=> 'c) \<Rightarrow> ('a =proc=> 'b =proc=> 'c)"
lemma red_procfun_apply_curry:
  fixes p
  assumes "procfun_apply p (arg_proc1,arg_proc2) = q"
  defines "p0 == curry_proc p"
  shows "procfun_apply (procfun_apply p0 arg_proc1) arg_proc2 = q"
sorry

lemma procfun_apply_ex:
  fixes p body body0 retval args
  assumes "subst_prog1 arg_proc body = PROGRAM[\<guillemotleft>body0\<guillemotright>]"
  defines "p0==procedure_functor_mk_typed (Proc body (Rep_procargvars args) (mk_expression_untyped retval))"
  shows "procfun_apply p0 arg_proc = \<lparr> p_body=body0, p_args=args, p_return=retval \<rparr>"
sorry

lemma subst_prog1_seq:
  assumes "subst_prog1 p q1 = PROGRAM[\<guillemotleft>c1\<guillemotright>]"
  assumes "subst_prog1 p q2 = PROGRAM[\<guillemotleft>c2\<guillemotright>]"
  defines "q == Seq q1 q2"
  shows "subst_prog1 p q = PROGRAM[\<guillemotleft>c1\<guillemotright>; \<guillemotleft>c2\<guillemotright>]"
sorry

lemma subst_prog1_closed:
  fixes q c p
  defines "q == mk_program_untyped c"
  shows "subst_prog1 p q = PROGRAM[\<guillemotleft>c\<guillemotright>]"
sorry

term callproc

lemma subst_prog1_callproc:
  fixes v args
  defines "q==CallProc (mk_variable_untyped v) (ProcRef 0) (mk_procargs_untyped procargs_empty)"
  shows "subst_prog1 p q = PROGRAM[v:=CALL p()]"
sorry

definition "x == Variable ''x'' :: int variable"
definition "y == Variable ''y'' :: unit variable"
schematic_lemma l1:
  shows "\<And>p q r. my_proc == ?my_proc \<Longrightarrow> 
  (procfun_apply my_proc (p,q,r) = proc() { x:=1; y:=CALL p(); y:=CALL q(); return () })"
apply (drule meta_eq_to_obj_eq, hypsubst, thin_tac "?a = ?b")
apply (rule procfun_apply_ex)
apply (rule subst_prog1_seq)
apply (rule subst_prog1_seq)
apply (rule subst_prog1_closed)
apply (rule subst_prog1_callproc)
apply (rule subst_prog1_callproc)
by (tactic all_tac)

definition my_proc_def0: "my_proc \<equiv>
 procedure_functor_mk_typed
  (Proc (Seq (mk_program_untyped (assign x (const_expression 1)))
          (CallProc (mk_variable_untyped y) (ProcRef 0) (mk_procargs_untyped procargs_empty)))
    (mk_procargvars_untyped procargvars_empty)
    (mk_expression_untyped (const_expression ())))"

lemmas my_proc_def = my_proc_def0[THEN l1]
end
