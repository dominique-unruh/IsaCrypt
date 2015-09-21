theory Lang_Typed
imports Lang_Untyped TermX_Antiquot
begin

subsection {* Types *}
  
definition "Type (_::('a::prog_type) itself) 
    = Abs_type \<lparr> tr_domain=range (embedding::'a\<Rightarrow>val),
                 tr_default=embedding (default::'a) \<rparr>"

lemma bool_type: "bool_type = Type TYPE(bool)"
  unfolding bool_type_def Type_def ..

lemma embedding_Type: "embedding (x::'a::prog_type) \<in> t_domain (Type TYPE('a))"
  unfolding Type_def t_domain_def
  by (subst Abs_type_inverse, auto)
lemma embedding_Type_range: "range (embedding::'a\<Rightarrow>val) = t_domain (Type TYPE('a::prog_type))"
  unfolding Type_def t_domain_def
  by (subst Abs_type_inverse, auto)

lemma t_default_Type [simp]: "t_default (Type TYPE('a::prog_type)) = embedding (default::'a)"
  by (simp add: Abs_type_inverse t_default_def Type_def)


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
  unfolding var_eq_def memory_update_def memory_lookup_def 
  apply simp apply (subst memory_lookup_update_same_untyped)
  by (simp_all add: embedding_Type)
lemma memory_lookup_update_notsame [simp]: 
  "\<not>var_eq v w \<Longrightarrow> memory_lookup (memory_update m v a) w == memory_lookup m w"
  unfolding var_eq_def memory_lookup_def memory_update_def
  by (simp add: memory_lookup_update_notsame_untyped)  
  
lemma memory_lookup_untyped_mk_variable_untyped [simp]:
  "memory_lookup_untyped m (mk_variable_untyped x) = embedding (memory_lookup m x)"
proof -
  def v == "memory_lookup_untyped m (mk_variable_untyped x)"
  have v_type: "v \<in> t_domain (Type TYPE('a))"
    by (metis v_def memory_lookup_untyped_type mk_variable_untyped_type)
  have v_range: "v \<in> range (embedding::'a\<Rightarrow>val)"
    by (simp add: embedding_Type_range v_type)
  have "v = embedding (inv embedding v :: 'a)"
    by (simp add: v_range f_inv_into_f)
  thus ?thesis unfolding v_def memory_lookup_def .
qed

subsection {* Expressions *}

record 'a expression_rep =
  er_fun :: "memory \<Rightarrow> 'a"
  er_vars :: "variable_untyped list"
typedef 'a expression = "{(e::'a expression_rep).
  (\<forall>m1 m2. (\<forall>v\<in>set (er_vars e). memory_lookup_untyped m1 v = memory_lookup_untyped m2 v) \<longrightarrow> er_fun e m1 = er_fun e m2)}"
  by (rule exI[of _ "\<lparr> er_fun=(\<lambda>m. undefined),
                       er_vars=[] \<rparr>"], simp)
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
    close (metis expression_rep.select_convs(1) expression_rep.select_convs(2) f_touches rep_abs)
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
  unfolding e_fun_def e_vars_def using Rep_expression by auto
lemma mk_expression_untyped_type [simp]: "eu_type (mk_expression_untyped (e::'a::prog_type expression)) = Type TYPE('a)"
  unfolding mk_expression_untyped_def eu_type_def
  apply (subst Abs_expression_untyped_inverse, auto simp: embedding_Type)
  unfolding e_fun_def e_vars_def using Rep_expression by blast
lemma mk_expression_untyped_vars [simp]: "eu_vars (mk_expression_untyped (e::'a::prog_type expression)) = e_vars e"
  unfolding mk_expression_untyped_def eu_vars_def
  apply (subst Abs_expression_untyped_inverse, auto simp: embedding_Type)
  unfolding e_fun_def e_vars_def using Rep_expression by blast
lemma e_fun_bool_untyped: "e_fun (e::bool expression) m = (eu_fun (mk_expression_untyped e) m = embedding True)"
  by (metis (poly_guards_query) embedding_inv mk_expression_untyped_fun)

lemma mk_expression_untyped_inverse: "mk_expression_typed (mk_expression_untyped e) = e"
  unfolding mk_expression_typed_def apply simp
  by (metis (full_types) Rep_expression_inverse e_fun_def e_vars_def expression_rep.surjective unit.exhaust)

definition "mk_expression_distr (e::('a::prog_type)distr expression) =
  Abs_expression_distr \<lparr> edr_fun=\<lambda>m. apply_to_distr embedding (e_fun e m),
                         edr_type=Type TYPE('a),
                         edr_vars=e_vars e \<rparr>"

lemma mk_expression_distr_fun [simp]: "ed_fun (mk_expression_distr (e::'a::prog_type distr expression)) m = apply_to_distr embedding (e_fun e m)"
  unfolding mk_expression_distr_def ed_fun_def
  apply (subst Abs_expression_distr_inverse, auto simp: embedding_Type)
  unfolding e_fun_def e_vars_def 
  using Rep_expression[of e] by auto

lemma mk_expression_distr_type [simp]: "ed_type (mk_expression_distr (e::'a::prog_type distr expression)) = Type TYPE('a)"
  unfolding mk_expression_distr_def ed_type_def
  apply (subst Abs_expression_distr_inverse, auto simp: embedding_Type)
  unfolding e_fun_def e_vars_def 
  using Rep_expression[of e] by auto


definition const_expression :: "'a \<Rightarrow> 'a expression" where
  "const_expression x = Abs_expression \<lparr> er_fun=\<lambda>m. x, er_vars=[] \<rparr>"
lemma e_fun_const_expression [simp]: "e_fun (const_expression a) = (\<lambda>m. a)"
  unfolding const_expression_def e_fun_def
  by (subst Abs_expression_inverse, auto)
lemma e_vars_const_expression [simp]: "e_vars (const_expression x) = []"
  by (simp add: e_vars_def const_expression_def Abs_expression_inverse) 

definition apply_expression :: "('a\<Rightarrow>'b)expression \<Rightarrow> ('a::prog_type) variable \<Rightarrow> 'b expression" where
"apply_expression e v = Abs_expression
  \<lparr> er_fun=\<lambda>m. (e_fun e m) (memory_lookup m v),
    er_vars=mk_variable_untyped v#e_vars e \<rparr>"
lemma e_fun_apply_expression [simp]: "e_fun (apply_expression e v) = (\<lambda>m. (e_fun e m) (memory_lookup m v))"
  unfolding apply_expression_def e_fun_def e_vars_def memory_lookup_def
  apply (subst Abs_expression_inverse, auto)
  using Rep_expression by fastforce
lemma e_vars_apply_expression [simp]: "e_vars (apply_expression e v) = mk_variable_untyped v # e_vars e"
  unfolding apply_expression_def e_vars_def e_fun_def memory_lookup_def apply (subst Abs_expression_inverse, auto)
  using Rep_expression by fastforce

definition var_expression :: "('a::prog_type) variable \<Rightarrow> 'a expression" where
"var_expression v = Abs_expression
  \<lparr> er_fun=\<lambda>m. memory_lookup m v,
    er_vars=[mk_variable_untyped v] \<rparr>"
lemma e_fun_var_expression [simp]: "e_fun (var_expression v) = (\<lambda>m. memory_lookup m v)"
  unfolding e_fun_def var_expression_def memory_lookup_def
  by (subst Abs_expression_inverse, auto)

subsection {* Procedures *}

(*class procargs =
  fixes procargs_len :: "'a itself \<Rightarrow> nat"
  fixes procargtypes :: "'a itself \<Rightarrow> type list" 
  assumes procargtypes_len: "length (procargtypes TYPE('a)) = procargs_len TYPE('a)"

definition "procargs (_::'a::procargs itself) == {vs. map eu_type vs = procargtypes TYPE('a)}"
lemma procargs_not_empty: "procargs (TYPE(_)) \<noteq> {}"
  unfolding procargs_def apply auto
  by (metis ex_map_conv expression_type_inhabited)

lemma procargs_len: "\<forall>x\<in>procargs TYPE('a::procargs). length x = procargs_len TYPE('a)"
  unfolding procargs_def by (metis (full_types) length_map procargtypes_len mem_Collect_eq) 

(*lemma procargs_typematch'': "\<forall>vs\<in>procargs TYPE('a::procargs). map eu_type vs = procargtypes TYPE('a)"
  unfolding procargs_def by auto*)

definition procargvars :: "'a::procargs itself \<Rightarrow> variable_untyped list set" where
  "procargvars _ = {vs. distinct vs \<and> map vu_type vs = procargtypes TYPE('a) \<and> 
                    (\<forall>v\<in>set vs. \<not> vu_global v)}"
lemma procargvars_inhabited: "procargvars TYPE('a::procargs) \<noteq> {}" 
  unfolding procargvars_def apply auto
  apply (rule exI[of _ "fresh_variables_local [] (procargtypes TYPE('a)) :: variable_untyped list"])
  using fresh_variables_local_distinct fresh_variables_local_local fresh_variables_local_type 
  by auto

lemma procargvars_local: "\<forall>l\<in>procargvars TYPE('a::procargs). \<forall>v\<in>set l. \<not> vu_global v"
  unfolding procargvars_def by auto
lemma procargvars_distinct: "\<forall>vs\<in>procargvars TYPE('a::procargs). distinct vs"
  unfolding procargvars_def by auto
(*lemma procargs_typematch: "\<forall>es\<in>procargs TYPE('a::procargs). \<forall>vs\<in>procargvars TYPE('a). 
     map vu_type vs = map eu_type es"
   unfolding procargvars_def procargs_def by auto*)

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
lemma vu_type_procargs [simp]: "map eu_type (mk_procargs_untyped (pargs::'a procargs)) = procargtypes TYPE('a::procargs)"
  using Rep_procargs unfolding procargs_def by auto
typedef ('a::procargs) procargvars = "procargvars TYPE('a)" using procargvars_inhabited by auto
abbreviation "mk_procargvars_untyped == Rep_procargvars"
lemma vu_type_procargvars [simp]: "map vu_type (mk_procargvars_untyped (pargs::'a procargvars)) = procargtypes TYPE('a::procargs)"
  using Rep_procargvars unfolding procargvars_def by auto


definition "vars_procargs p = [x. e<-mk_procargs_untyped p, x<-eu_vars e]" *)

typedef ('a::prog_type) pattern = "{pat. pu_type pat = Type TYPE('a)}"
  by (rule exI[of _ "pattern_ignore (Type TYPE('a))"], simp)
abbreviation "mk_pattern_untyped == Rep_pattern"
definition "p_vars p = pu_vars (mk_pattern_untyped p)"
lemma pu_type_mk_pattern_untyped [simp]: "pu_type (mk_pattern_untyped (p::'a pattern)) = Type TYPE('a::prog_type)"
  using Rep_pattern by simp

definition "memory_update_pattern m (v::'a pattern) (a::'a::prog_type) =
  memory_update_untyped_pattern m (mk_pattern_untyped v) (embedding a)"


record ('a,'b) procedure = 
  p_body :: program
  p_args :: "'a pattern" (* TODO rename p_arg *)
  p_return :: "'b expression"

definition "mk_procedure_untyped proc = 
  Proc (mk_program_untyped (p_body proc)) (Rep_pattern (p_args proc)) (mk_expression_untyped (p_return proc))"

fun mk_procedure_typed :: "procedure_rep \<Rightarrow> ('a::prog_type, 'b::prog_type, 'c) procedure_ext"  where
 "mk_procedure_typed (Proc body args return) = 
    \<lparr> p_body=Abs_program body, p_args=Abs_pattern args, p_return=mk_expression_typed return, \<dots> = undefined\<rparr>"
| "mk_procedure_typed _ = undefined"

class singleton = 
  fixes the_singleton::'a (* Why do we need this? *)
  assumes singleton_eq [simp]: "a=b"
instantiation unit :: singleton begin
  instance apply intro_classes by auto
end

lemma mk_procedure_untyped_inverse:
  shows "mk_procedure_typed (mk_procedure_untyped p) = (p::('a::prog_type,'b::prog_type,'c::singleton)procedure_ext)"
unfolding mk_procedure_untyped_def 
apply (cases p)
by (auto simp: Rep_program_inverse mk_expression_untyped_inverse Rep_pattern_inverse)

(* TODO remove *)
ML {*
Axclass.thynames_of_arity @{theory} (@{type_name bool},"Universe.prog_type")  

*}

lemma mk_procedure_typed_inverse:
  fixes body args return
  assumes "well_typed body"
  assumes "pu_type args = Type TYPE('a)"
  assumes "eu_type return = Type TYPE('b)"
  defines "p == Proc body args return"
  shows "mk_procedure_untyped (mk_procedure_typed p :: ('a::prog_type,'b::prog_type,'c)procedure_ext) = p"
  unfolding mk_procedure_untyped_def p_def apply auto
  apply (subst Abs_program_inverse, auto simp: assms)
  apply (simp add: Abs_pattern_inverse assms)
  by (subst mk_expression_typed_inverse, auto simp: assms)


definition "procedure_type (_::('a::prog_type,'b::prog_type,'c) procedure_ext itself) = 
  \<lparr> pt_argtype=Type TYPE('a), pt_returntype=Type TYPE('b) \<rparr>"

lemma mk_procedure_untyped:
  fixes p0::"('a::prog_type,'b::prog_type,'c)procedure_ext"
  defines "p == mk_procedure_untyped p0"
  shows "well_typed_proc p" and "proctype_of p = procedure_type TYPE(('a,'b,'c)procedure_ext)"
SORRY

(*
definition procargs_empty :: "unit procargs" where
  "procargs_empty = Abs_procargs []"
definition procargs_add :: "('a::prog_type) expression \<Rightarrow> ('b::procargs) procargs \<Rightarrow> ('a*'b) procargs" where
  "procargs_add e es = Abs_procargs (mk_expression_untyped e#Rep_procargs es)"
definition procargvars_empty :: "unit procargvars" where
  "procargvars_empty = Abs_procargvars []"
definition procargvars_add :: "('a::prog_type) variable \<Rightarrow> ('b::procargs) procargvars \<Rightarrow> ('a*'b) procargvars" where
  "procargvars_add v vs = Abs_procargvars (mk_variable_untyped v#Rep_procargvars vs)"
*)

(*
lemma procedure_type_procargvars:
  assumes procT: "proctype_of (Proc body args ret) = procedure_type TYPE(('a::procargs,'b::prog_type,'c)procedure_ext)"
  and wt: "well_typed_proc (Proc body args ret)"
  shows "args \<in> procargvars TYPE('a)"
proof -
  from procT have t: "procargtypes TYPE('a) = map vu_type args"
    by (simp add: procedure_type_def)
  from wt have dist_glob: "distinct args \<and> (\<forall>v\<in>set args. \<not> vu_global v)"
    by simp
  show "args \<in> procargvars TYPE('a)"
    unfolding procargvars_def apply (simp add: dist_glob)
    unfolding t list_all2_map2 by simp
qed
*)

(*
lemma procargvars_add_untyped [simp]: "mk_procargvars_untyped (procargvars_add x a) = mk_variable_untyped x # mk_procargvars_untyped a" SORRY
lemma procargvars_empty_untyped [simp]: "mk_procargvars_untyped procargvars_empty = []" SORRY
lemma procargs_add_untyped [simp]: "mk_procargs_untyped (procargs_add x a) = mk_expression_untyped x # mk_procargs_untyped a" SORRY
lemma procargs_empty_untyped [simp]: "mk_procargs_untyped procargs_empty = []" SORRY
lemma vars_procargs_add [simp]: "vars_procargs (procargs_add e a) = e_vars e @ vars_procargs a" SORRY
lemma vars_procargs_empty [simp]: "vars_procargs procargs_empty = []" SORRY
*)





subsection {* Typed programs *}

definition "label (l::string) (p::program) = p"

definition "seq p q = Abs_program (Seq (mk_program_untyped p) (mk_program_untyped q))"

lemma mk_untyped_seq [simp]: "mk_program_untyped (seq p q) = Seq (mk_program_untyped p) (mk_program_untyped q)"
  unfolding seq_def denotation_def apply (subst Abs_program_inverse) by auto

definition "skip = Abs_program Skip"

lemma mk_untyped_skip [simp]: "mk_program_untyped skip = Skip"
  unfolding skip_def denotation_def apply (subst Abs_program_inverse) by auto

definition "assign (v::('a::prog_type) variable) (e::'a expression) =
  Abs_program (Assign (pattern_1var (mk_variable_untyped v)) (mk_expression_untyped e))"

lemma mk_untyped_assign [simp]: "mk_program_untyped (assign (v::'a::prog_type variable) e) = 
  Assign (pattern_1var (mk_variable_untyped v)) (mk_expression_untyped e)"
  unfolding assign_def denotation_def apply (subst Abs_program_inverse) by (simp_all)
  
definition "sample (v::('a::prog_type) variable) (e::'a distr expression) =
  Abs_program (Sample (pattern_1var (mk_variable_untyped v)) (mk_expression_distr e))"

lemma mk_untyped_sample [simp]: "mk_program_untyped (sample (v::'a::prog_type variable) e)
   = Sample (pattern_1var (mk_variable_untyped v)) (mk_expression_distr e)"
  unfolding sample_def denotation_def apply (subst Abs_program_inverse) by simp_all 

definition ifte :: "bool expression \<Rightarrow> program \<Rightarrow> program \<Rightarrow> program" where
  "ifte e thn els = Abs_program (IfTE (mk_expression_untyped e) (mk_program_untyped thn) (mk_program_untyped els))"

lemma mk_untyped_ifte [simp]: "mk_program_untyped (ifte e thn els) =
  IfTE (mk_expression_untyped e) (mk_program_untyped thn) (mk_program_untyped els)"
  unfolding ifte_def denotation_def apply (subst Abs_program_inverse) using bool_type by auto

definition while :: "bool expression \<Rightarrow> program \<Rightarrow> program" where
  "while e p = Abs_program (While (mk_expression_untyped e) (mk_program_untyped p))"

lemma mk_untyped_while [simp]: "mk_program_untyped (while e p) =
  While (mk_expression_untyped e) (mk_program_untyped p)"
  unfolding while_def denotation_def apply (subst Abs_program_inverse) using bool_type by auto

definition callproc :: "'a::prog_type pattern \<Rightarrow> ('b::prog_type,'a) procedure \<Rightarrow> 'b expression \<Rightarrow> program" where
  "callproc v proc args = Abs_program (CallProc (mk_pattern_untyped v) (mk_procedure_untyped proc) (mk_expression_untyped args))"

lemma list_all2_swap: "list_all2 P x y = list_all2 (\<lambda>x y. P y x) y x"
  by (metis list_all2_conv_all_nth)

lemma mk_untyped_callproc [simp]: "mk_program_untyped (callproc v proc args) =
  CallProc (mk_pattern_untyped v) (mk_procedure_untyped proc) (mk_expression_untyped args)"
proof -
  have swap: "\<And>x y. list_all2 (\<lambda>(x::variable_untyped) y. vu_type x = eu_type y) x y = list_all2 (\<lambda>y x. eu_type y = vu_type x) y x"
   unfolding list_all2_conv_all_nth by auto
  show ?thesis
  unfolding callproc_def denotation_def mk_procedure_untyped_def 
  by (subst Abs_program_inverse, auto)
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
  unfolding denotation_def memory_update_def[THEN ext] mk_untyped_sample by simp

lemma denotation_ifte: "denotation (ifte e thn els) m = (if e_fun e m then denotation thn m else denotation els m)"
  unfolding denotation_def mk_untyped_ifte by simp
lemma denotation_while: "denotation (while e p) m = Abs_distr (\<lambda>m'. \<Sum>n. Rep_distr (compose_distr (\<lambda>m. if e_fun e m then 0 else point_distr m)
                                                  (while_iter n (e_fun e) (denotation p) m)) m')"
  unfolding denotation_def mk_untyped_while by simp 

lemma denotation_callproc: "denotation (callproc v proc args) m =
  (let argval = e_fun args m in
  let m' = init_locals m in
  let m' = memory_update_pattern m' (p_args proc) argval in
  apply_to_distr (\<lambda>m'.
    let res = e_fun (p_return proc) m' in
    let m' = restore_locals m m' in
    memory_update_pattern m' v res)
  (denotation (p_body proc) m'))"
  unfolding denotation_def mk_untyped_callproc mk_procedure_untyped_def memory_update_pattern_def by simp

lemma denotation_seq_skip [simp]: "denotation (seq Lang_Typed.skip c) = denotation c"
  unfolding denotation_seq[THEN ext] mk_untyped_skip denotation_def by simp 
lemma denotation_skip_seq [simp]: "denotation (seq c Lang_Typed.skip) = denotation c"
  unfolding denotation_seq[THEN ext] mk_untyped_skip denotation_def denotation_untyped_Skip[THEN ext]
  by simp 

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

print_syntax
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
syntax "_callproc" :: "idt \<Rightarrow> ('a,'b) procedure \<Rightarrow> tuple_syntax \<Rightarrow> program_syntax" ("_ := call _ (_)" 30)
syntax "" :: "program_syntax \<Rightarrow> program_syntax" ("{ _ }")
syntax "" :: "program_syntax \<Rightarrow> program_syntax" ("'(_')")
syntax "" :: "program_syntax \<Rightarrow> program_syntax" ("'(_;')")
syntax "" :: "program_syntax \<Rightarrow> program_syntax" ("{ _; }")
syntax "_var_access" :: "'a variable \<Rightarrow> 'a" ("$_" [1000] 999)
definition program :: "program \<Rightarrow> program" where "program p = p"

(*syntax "_local_vars" :: "idts \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("local _;/ _" [0,9] 9) *)
syntax "_local_vars_global" :: "idts \<Rightarrow> 'b \<Rightarrow> 'b" ("(3LOCAL _./ _)" 100)

subsubsection {* Translation functions *}

ML_file "lang_syntax.ML"

parse_translation {* [("_program", fn ctx => fn p => 
    Const(@{const_syntax program},dummyT) $ 
      Lang_Syntax.translate_program ctx (Unsynchronized.ref[]) (hd p))] *}

print_translation {* [(@{const_syntax program}, fn ctx => fn p => Const("_program",dummyT) $ Lang_Syntax.translate_program_back ctx (hd p))] *}

parse_translation {* [("_local_vars_global", fn ctx => fn p =>
  case p of [vs,body] =>
  Lang_Syntax.translate_local_vars_global ctx vs body)] *}

subsection {* Concrete grammar for procedures *}

nonterminal procedure_decl_args_syntax
nonterminal procedure_decl_args_syntax'
syntax "_procedure_decl_args_none" :: procedure_decl_args_syntax ("'(')")
syntax "_procedure_decl_args_single" :: "idt \<Rightarrow> procedure_decl_args_syntax'" ("_")
syntax "_procedure_decl_args_cons" :: "idt \<Rightarrow> procedure_decl_args_syntax' \<Rightarrow> procedure_decl_args_syntax'" ("_,_")
syntax "" :: "procedure_decl_args_syntax' \<Rightarrow> procedure_decl_args_syntax" ("'(_')")
syntax "_procedure_decl" :: "procedure_decl_args_syntax \<Rightarrow> program_syntax \<Rightarrow> 'b \<Rightarrow> ('a,'b) procedure" ("proc _ {_; return _}")
syntax "_procedure_decl" :: "procedure_decl_args_syntax \<Rightarrow> program_syntax \<Rightarrow> 'b \<Rightarrow> ('a,'b) procedure" ("proc _ {_; return _;}")

definition "TODO_REMOVE_ME == undefined"

parse_translation {* [("_procedure_decl", fn ctx => fn [args,body,return] => 
let val known = Unsynchronized.ref[] (* TODO: add local vars *)
    fun trargs (Const("_procedure_decl_args_none",_)) = Const(@{const_name TODO_REMOVE_ME},dummyT)
      | trargs (Const("_procedure_decl_args_single",_)$x) = 
          (Lang_Syntax.add_var known x; Const(@{const_name TODO_REMOVE_ME},dummyT) $ x $ Const(@{const_name TODO_REMOVE_ME},dummyT))
      | trargs (Const("_procedure_decl_args_cons",_)$x$xs) = 
          (Lang_Syntax.add_var known x; Const(@{const_name TODO_REMOVE_ME},dummyT) $ x $ trargs xs)
      | trargs t = raise (TERM ("trargs",[t]))
    val args = trargs args
in
Const(@{const_name Lang_Typed.procedure.procedure_ext},dummyT) $ 
   Lang_Syntax.translate_program ctx known body $ (* p_body *)
   args $ (* p_args *)
   Lang_Syntax.translate_expression ctx known return $ (* p_return *)
   Const(@{const_name Product_Type.Unity},dummyT)
end)] *}


lemma vars_seq [simp]: "vars (seq a b) = vars a @ vars b" by (simp add: vars_def)
lemma vars_assign [simp]: "vars (assign x e) = mk_variable_untyped x # e_vars e" SORRY
lemma vars_sample [simp]: "vars (sample x e) = mk_variable_untyped x # e_vars e" SORRY
lemma vars_while [simp]: "vars (Lang_Typed.while e p) = e_vars e @ vars p" by (simp add: vars_def)
lemma vars_ifte [simp]: "vars (Lang_Typed.ifte e p1 p2) = e_vars e @ vars p1 @ vars p2" by (simp add: vars_def)
definition "vars_proc_global p == [v. v<-p_vars (p_args p), vu_global v] @ [v. v<-vars (p_body p), vu_global v] @ [v. v<-e_vars (p_return p), vu_global v]"
lemma vars_callproc [simp]: "vars (callproc x p a) = p_vars x @ e_vars a @ vars_proc_global p"
  unfolding vars_def vars_proc_global_def p_vars_def by (auto simp: mk_procedure_untyped_def)
lemma vars_skip [simp]: "vars Lang_Typed.skip = []" by (simp add: vars_def)
lemma LVariable_local [simp]: "\<not> vu_global (mk_variable_untyped (LVariable x))"
  by (simp add: mk_variable_untyped_def)
lemma Variable_global [simp]: "vu_global (mk_variable_untyped (Variable x))"
  by (simp add: mk_variable_untyped_def)
lemma mk_variable_untyped_distinct1 [simp]: "a \<noteq> b \<Longrightarrow> mk_variable_untyped (LVariable a) \<noteq> mk_variable_untyped (LVariable b)"
  by (simp add: mk_variable_untyped_def)
lemma mk_variable_untyped_distinct2 [simp]: "mk_variable_untyped (LVariable a) \<noteq> mk_variable_untyped (Variable b)"
  by (simp add: mk_variable_untyped_def)
lemma mk_variable_untyped_distinct3 [simp]: "mk_variable_untyped (Variable a) \<noteq> mk_variable_untyped (LVariable b)"
  by (simp add: mk_variable_untyped_def)

end
