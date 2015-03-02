theory Lang_Typed
imports Lang_Untyped
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
  by (metis embedding_inv f_inv_into_f memory_lookup_update_same_untyped rangeI)
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
lemma mk_expression_untyped_fun [simp]: "eu_fun (mk_expression_untyped (e::'a::prog_type expression)) m = embedding (e_fun e m)"
  unfolding mk_expression_untyped_def eu_fun_def
  apply (subst Abs_expression_untyped_inverse, auto simp: embedding_Type)
  by (smt2 Rep_expression e_fun_def e_vars_def mem_Collect_eq)
lemma mk_expression_untyped_type [simp]: "eu_type (mk_expression_untyped (e::'a::prog_type expression)) = Type TYPE('a)"
  unfolding mk_expression_untyped_def eu_type_def
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
  fixes procargs :: "'a itself \<Rightarrow> expression_untyped list set"
  fixes procargvars :: "'a itself \<Rightarrow> variable_untyped list set"
  assumes procargs_not_empty: "procargs (TYPE('a)) \<noteq> {}"
  assumes procargvars_not_empty: "procargvars (TYPE('a)) \<noteq> {}"
  assumes procargvars_local: "\<forall>l\<in>procargvars (TYPE('a)). \<forall>v\<in>set l. \<not> vu_global v"
  assumes procargs_len: "\<forall>x\<in>procargs TYPE('a). length x = procargs_len TYPE('a)"
  assumes procargvars_len: "\<forall>x\<in>procargvars TYPE('a). length x = procargs_len TYPE('a)"
  assumes procargs_typematch: "\<forall>es\<in>procargs TYPE('a). \<forall>vs\<in>procargvars TYPE('a). 
     list_all2 (\<lambda>v e. vu_type v = eu_type e) vs es"
  assumes procargvars_distinct: "\<forall>vs\<in>procargvars TYPE('a). distinct vs"

instantiation unit :: procargs begin
definition "procargs (_::unit itself) = {[]::expression_untyped list}"
definition "procargvars (_::unit itself) = {[]::variable_untyped list}"
definition "procargs_len (_::unit itself) = 0"
instance apply intro_classes unfolding procargs_unit_def procargvars_unit_def procargs_len_unit_def by auto
end

definition "freshvar vs = (SOME vn. \<forall>v\<in>set vs. vn \<noteq> vu_name v)"
lemma freshvar_global: "mk_variable_untyped (Variable (freshvar vs)) \<notin> set vs"
  sorry
lemma freshvar_local: "mk_variable_untyped (LVariable (freshvar vs)) \<notin> set vs"
  sorry

instantiation prod :: (prog_type,procargs) procargs begin
definition "procargs_len (_::('a::prog_type*'b) itself) = Suc (procargs_len TYPE('b))"
definition "procargs (_::('a::prog_type*'b) itself) = {mk_expression_untyped e#es|(e::'a expression) es. es\<in>procargs TYPE('b)}"
definition "procargvars (_::('a::prog_type*'b) itself)= {mk_variable_untyped (LVariable v::'a variable)#vs|v vs. vs\<in>procargvars TYPE('b) \<and> mk_variable_untyped (LVariable v::'a variable)\<notin>set vs}"
instance apply intro_classes unfolding procargs_prod_def procargvars_prod_def procargs_len_prod_def mk_variable_untyped_def
         apply (auto simp: procargs_not_empty procargvars_not_empty procargs_len procargvars_len procargs_typematch)
         apply (metis ex_in_conv freshvar_local mk_variable_untyped_def procargvars_not_empty variable.simps(6))
         apply (metis procargvars_local)
         by (metis procargvars_distinct)
end

typedef ('a::procargs) procargs = "procargs TYPE('a)" using procargs_not_empty by auto
abbreviation "mk_procargs_untyped == Rep_procargs"
typedef ('a::procargs) procargvars = "procargvars TYPE('a)" using procargvars_not_empty by auto
abbreviation "mk_procargvars_untyped == Rep_procargvars"
(* TODO: procargvars should be all disjoint *)

record ('a::procargs,'b) procedure = 
  p_body :: program
  p_args :: "'a procargvars"
  p_return :: "'b expression"
definition "mk_procedure_untyped proc = 
  Proc (mk_program_untyped (p_body proc)) (Rep_procargvars (p_args proc)) (mk_expression_untyped (p_return proc))"

definition procargs_empty :: "unit procargs" where
  "procargs_empty = Abs_procargs []"
definition procargs_add :: "('a::prog_type) expression \<Rightarrow> ('b::procargs) procargs \<Rightarrow> ('a*'b) procargs" where
  "procargs_add e es = Abs_procargs (mk_expression_untyped e#Rep_procargs es)"
definition procargvars_empty :: "unit procargvars" where
  "procargvars_empty = Abs_procargvars []"
definition procargvars_add :: "('a::prog_type) variable \<Rightarrow> ('b::procargs) procargvars \<Rightarrow> ('a*'b) procargvars" where
  "procargvars_add v vs = Abs_procargvars (mk_variable_untyped v#Rep_procargvars vs)"

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

lemma mk_untyped_callproc: "mk_program_untyped (callproc v proc args) =
  CallProc (mk_variable_untyped v) (mk_procedure_untyped proc) (mk_procargs_untyped args)"
  unfolding callproc_def denotation_def mk_procedure_untyped_def 
  apply (subst Abs_program_inverse, auto)
  apply (metis Rep_procargs Rep_procargvars procargs_typematch)
  apply (metis Rep_procargvars list_all_iff procargvars_local)
  by (metis Rep_procargvars procargvars_distinct)

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
lemma denotation_while: "denotation (while e p) m = ell1_to_distr (\<Sum>n. distr_to_ell1 (compose_distr (\<lambda>m. if e_fun e m then 0 else point_distr m)
                                                  (while_iter n (e_fun e) (denotation p) m)))"
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
lemma denotation_trans: "denotation (seq (seq x y) z) = denotation (seq x (seq y z))"
  unfolding denotation_seq[THEN ext] 
  unfolding compose_distr_trans ..


subsection {* Concrete syntax for programs *}

subsubsection {* Grammar *}

nonterminal program_syntax

(* TODO: grammar callproc *)

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

end
