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

lemma embedding_inv_embedding:
  assumes "x \<in> t_domain (Type TYPE('a::prog_type))"
  shows "embedding (inv embedding x :: 'a) = x"
unfolding inv_def apply (rule exE_some[where P="\<lambda>y. embedding y = x"])
using assms unfolding embedding_Type_range[symmetric] by auto


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

lemma vu_name_make_variable_untyped1 [simp]: "vu_name (mk_variable_untyped (Variable n)) = n"
  unfolding mk_variable_untyped_def by simp
lemma vu_name_make_variable_untyped2 [simp]: "vu_name (mk_variable_untyped (LVariable n)) = n"
  unfolding mk_variable_untyped_def by simp

definition mk_variable_typed :: "variable_untyped \<Rightarrow> 'a::prog_type variable" where
  "mk_variable_typed v = (if vu_global v then Variable (vu_name v) else LVariable (vu_name v))"
lemma mk_variable_untyped_inverse [simp]: "mk_variable_typed (mk_variable_untyped v) = v"
  by (cases v, simp_all add: mk_variable_typed_def mk_variable_untyped_def)
lemma mk_variable_untyped_inject: "(mk_variable_untyped x = mk_variable_untyped y) = (x = y)"
  by (metis mk_variable_untyped_inverse)
lemma mk_variable_typed_inverse: 
  assumes "vu_type x = Type TYPE('a::prog_type)"
  shows "mk_variable_untyped (mk_variable_typed x :: 'a variable) = x"
using assms by (cases x, simp_all add: mk_variable_typed_def mk_variable_untyped_def)


subsection {* Memories *}

definition "memory_lookup m (v::'a variable) :: ('a::prog_type) == inv embedding (memory_lookup_untyped m (mk_variable_untyped v))"
definition "memory_update m (v::'a variable) (a::'a::prog_type) =
  memory_update_untyped m (mk_variable_untyped v) (embedding a)"

lemma Rep_memory_update [simp]:
  shows "Rep_memory (memory_update m x v) = (Rep_memory m)(mk_variable_untyped x := embedding v)"
  unfolding memory_update_def by (subst Rep_memory_update_untyped', auto simp: embedding_Type)

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

lemma memory_update_lookup: "memory_update m x (memory_lookup m x) = m"
  unfolding memory_update_def memory_lookup_def
  apply (rule Rep_memory_inject[THEN iffD1], simp)
  unfolding  memory_lookup_def
  apply (subst embedding_inv_embedding)
   close (simp add: embedding_Type)
  apply (subst memory_update_lookup_untyped)
  by rule

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
lemma Rep_mk_expression_untyped [simp]: 
  "Rep_expression_untyped (mk_expression_untyped (e::('a::prog_type)expression)) =
  \<lparr> eur_fun=\<lambda>m. embedding (e_fun e m), eur_type=Type TYPE('a), eur_vars=e_vars e \<rparr>"
unfolding mk_expression_untyped_def
apply (subst Abs_expression_untyped_inverse) 
using Rep_expression by (auto simp: embedding_Type e_fun_def e_vars_def)

definition "mk_expression_typed (e::expression_untyped) = 
  Abs_expression \<lparr> er_fun=\<lambda>m. inv embedding (eu_fun e m),
                   er_vars=eu_vars e \<rparr>"
lemma Rep_mk_expression_typed [simp]: "Rep_expression (mk_expression_typed e) =
  \<lparr> er_fun=\<lambda>m. inv embedding (eu_fun e m), er_vars=eu_vars e \<rparr>"
      unfolding mk_expression_typed_def
      apply (subst Abs_expression_inverse, auto)
      using eu_fun_footprint by fastforce

lemma e_fun_eu_fun: "e_fun e = inv embedding o eu_fun (mk_expression_untyped e)"
  unfolding eu_fun_def Rep_mk_expression_untyped o_def by simp
lemma e_vars_eu_vars: "e_vars e = eu_vars (mk_expression_untyped e)"
  unfolding eu_vars_def Rep_mk_expression_untyped o_def by simp

lemma e_fun_footprint: 
  assumes "\<And>v. v\<in>set (e_vars e) \<Longrightarrow> memory_lookup_untyped m1 v = memory_lookup_untyped m2 v"
  shows "e_fun (e::'a::prog_type expression) m1 = e_fun e m2"
unfolding e_fun_eu_fun o_def
apply (tactic \<open>cong_tac @{context} 1\<close>, simp)
apply (subst eu_fun_footprint)
using assms unfolding e_vars_eu_vars by auto

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

lemma mk_expression_untyped_inject: "(mk_expression_untyped a = mk_expression_untyped b) = (a=b)"
  by (metis mk_expression_untyped_inverse)

definition "mk_expression_distr (e::('a::prog_type)distr expression) =
  Abs_expression_distr \<lparr> edr_fun=\<lambda>m. apply_to_distr embedding (e_fun e m),
                         edr_type=Type TYPE('a),
                         edr_vars=e_vars e \<rparr>"
lemma Rep_mk_expression_distr: "Rep_expression_distr (mk_expression_distr (e::('a::prog_type)distr expression)) =
  \<lparr> edr_fun=\<lambda>m. apply_to_distr embedding (e_fun e m),
    edr_type=Type TYPE('a),
    edr_vars=e_vars e \<rparr>"
      unfolding mk_expression_distr_def
      apply (subst Abs_expression_distr_inverse, auto)
       using embedding_Type_range close blast
      by (metis embedding_inv' eu_fun_footprint mk_expression_untyped_fun mk_expression_untyped_vars)

definition mk_expression_distr_typed :: "expression_distr \<Rightarrow> 'a::prog_type distr expression" where
  "mk_expression_distr_typed e = 
      Abs_expression \<lparr> er_fun=\<lambda>m. apply_to_distr (inv embedding) (ed_fun e m),
                     er_vars=ed_vars e \<rparr>"
lemma Rep_mk_expression_distr_typed: "Rep_expression (mk_expression_distr_typed e) =
  \<lparr> er_fun=\<lambda>m. apply_to_distr (inv embedding) (ed_fun e m), er_vars=ed_vars e \<rparr>"
      unfolding mk_expression_distr_typed_def
      apply (subst Abs_expression_inverse, auto)
      using ed_fun_footprint by fastforce

lemma mk_expression_distr_mk_expression_typed:
  fixes e :: expression_untyped
  assumes "eu_type e = Type TYPE('a distr)"
  shows "Rep_expression_distr (mk_expression_distr (mk_expression_typed e :: 'a::prog_type distr expression)) = 
    \<lparr> edr_fun = (\<lambda>x. apply_to_distr embedding (inv embedding x :: 'a distr)) o (eu_fun e), 
      edr_type=Type TYPE('a), edr_vars=eu_vars e \<rparr>"
apply (subst Rep_mk_expression_distr, auto simp: e_vars_def)
unfolding e_fun_def o_def
by (subst Rep_mk_expression_typed, simp)


lemma mk_expression_distr_typed_inverse:
  assumes "ed_type e=Type TYPE('a::prog_type)"
  shows "mk_expression_distr (mk_expression_distr_typed e :: 'a distr expression) = e"
proof -
  obtain f t v where e_parts: "Rep_expression_distr e = \<lparr>edr_fun=f, edr_type=t, edr_vars=v\<rparr>" 
      and f_supp: "\<And>m. support_distr (f m) \<subseteq> t_domain t"
        by (metis (mono_tags, lifting) Rep_expression_distr expression_distr_rep.surjective mem_Collect_eq old.unit.exhaust) 
  hence t: "t = Type TYPE('a)" using assms by (simp add: ed_type_def) 
  have F: "\<And>F \<mu>. (\<forall>x\<in>support_distr \<mu>. F x = x) \<Longrightarrow> apply_to_distr F \<mu> = \<mu>"
    using apply_to_distr_cong by fastforce
  have f: "\<And>m. apply_to_distr (\<lambda>x\<Colon>val. embedding (inv embedding x :: 'a)) (f m) = f m"
    apply (rule F) using f_supp t
    by (metis embedding_Type_range f_inv_into_f subsetCE)
  show ?thesis
    apply (rule Rep_expression_distr_inject[THEN iffD1])
    apply (subst Rep_mk_expression_distr)
    unfolding e_fun_def e_vars_def
    apply (subst Rep_mk_expression_distr_typed)+
    unfolding ed_vars_def ed_fun_def e_parts t
    using f by auto
qed

lemma mk_expression_distr_fun [simp]: "ed_fun (mk_expression_distr (e::'a::prog_type distr expression)) m = apply_to_distr embedding (e_fun e m)"
  unfolding mk_expression_distr_def ed_fun_def
  apply (subst Abs_expression_distr_inverse, auto simp: embedding_Type)
  unfolding e_fun_def e_vars_def 
  using Rep_expression[of e] by auto

lemma mk_expression_distr_vars [simp]: "ed_vars (mk_expression_distr (e::'a::prog_type distr expression)) = e_vars e"
  unfolding mk_expression_distr_def ed_vars_def
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
lemma mk_expression_untyped_const_expression:
  "mk_expression_untyped (const_expression (x::'a::prog_type)) = const_expression_untyped (Type TYPE('a)) (embedding x)"
  unfolding const_expression_def const_expression_untyped_def mk_expression_untyped_def e_fun_def e_vars_def
  by (subst Abs_expression_inverse, auto?)+


definition apply_expression :: "('a\<Rightarrow>'b)expression \<Rightarrow> ('a::prog_type) variable \<Rightarrow> 'b expression" where
"apply_expression e v = Abs_expression
  \<lparr> er_fun=\<lambda>m. (e_fun e m) (memory_lookup m v),
    er_vars=mk_variable_untyped v#e_vars e \<rparr>"
lemma Rep_apply_expression: "Rep_expression_untyped (mk_expression_untyped (apply_expression e v :: 'a expression)) =
  \<lparr> eur_fun=(\<lambda>m\<Colon>memory. embedding (e_fun e m (memory_lookup m v))),
    eur_type=Type TYPE('a::prog_type),
    eur_vars=mk_variable_untyped v # e_vars e \<rparr>"
  unfolding apply_expression_def 
  apply (auto simp: e_fun_def e_vars_def)
  apply (subst Abs_expression_inverse, auto) 
   close (smt Rep_expression e_vars_def mem_Collect_eq)
  apply (subst Abs_expression_inverse, auto)
  using Rep_expression by fastforce
  
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

typedef ('a::prog_type) pattern = "{pat. pu_type pat = Type TYPE('a)}"
  by (rule exI[of _ "pattern_ignore (Type TYPE('a))"], simp)
(* abbreviation "mk_pattern_untyped == Rep_pattern" *)
definition "p_vars p = pu_vars (Rep_pattern p)"
lemma Rep_pu_type [simp]: "pu_type (Rep_pattern (p::'a pattern)) = Type TYPE('a::prog_type)"
  using Rep_pattern by simp
definition "p_var_getters p = pu_var_getters (Rep_pattern p)"

definition "unit_pattern = (Abs_pattern (pattern_ignore unit_type) :: unit pattern)"
lemma Rep_unit_pattern: "Rep_pattern_untyped (Rep_pattern unit_pattern) = \<lparr> pur_var_getters=[], pur_type=Type TYPE(unit) \<rparr>"
  unfolding unit_pattern_def apply (subst Abs_pattern_inverse)
   close (simp add: Type_def unit_type_def)
  unfolding pattern_ignore_def apply (subst Abs_pattern_untyped_inverse)
   by (simp_all add: Type_def unit_type_def)

lemma vars_unit_pattern [simp]: "p_vars unit_pattern = []"
  unfolding p_vars_def unit_pattern_def apply (subst Abs_pattern_inverse) by (auto simp: Type_def unit_type_def)
definition "pair_pattern (p1::'a pattern) (p2::'b pattern) = (Abs_pattern (Abs_pattern_untyped 
  \<lparr> pur_var_getters=(map (\<lambda>(v,g). (v,g o embedding o fst o inv (embedding::'a*'b\<Rightarrow>_))) (p_var_getters p1))
                  @ (map (\<lambda>(v,g). (v,g o embedding o snd o inv (embedding::'a*'b\<Rightarrow>_))) (p_var_getters p2)),
    pur_type=Type TYPE('a::prog_type*'b::prog_type) \<rparr>) :: ('a*'b) pattern)"
lemma Rep_pair_pattern: "Rep_pattern_untyped (Rep_pattern (pair_pattern (p1::'a pattern) (p2::'b pattern))) = 
  \<lparr> pur_var_getters=(map (\<lambda>(v,g). (v,g o embedding o fst o inv (embedding::'a*'b\<Rightarrow>_))) (p_var_getters p1))
                  @ (map (\<lambda>(v,g). (v,g o embedding o snd o inv (embedding::'a*'b\<Rightarrow>_))) (p_var_getters p2)),
    pur_type=Type TYPE('a::prog_type*'b::prog_type) \<rparr>"
  unfolding pair_pattern_def  apply (subst Abs_pattern_inverse, simp)
  unfolding pu_type_def apply (subst Abs_pattern_untyped_inverse, auto)
  apply (metis (mono_tags, lifting) Rep_pattern_untyped mem_Collect_eq old.prod.case p_var_getters_def pu_var_getters_def)
  apply (metis (mono_tags, lifting) Rep_pattern_untyped mem_Collect_eq old.prod.case p_var_getters_def pu_var_getters_def)
  apply (subst Abs_pattern_untyped_inverse, auto)
  apply (metis (mono_tags, lifting) Rep_pattern_untyped mem_Collect_eq old.prod.case p_var_getters_def pu_var_getters_def)
  by (metis (mono_tags, lifting) Rep_pattern_untyped mem_Collect_eq old.prod.case p_var_getters_def pu_var_getters_def)

lemma var_getters_pair_pattern: "p_var_getters (pair_pattern (p1::'a::prog_type pattern) (p2::'b::prog_type pattern)) = 
    map (\<lambda>(v,g). (v, g \<circ> embedding \<circ> fst \<circ> inv (embedding::'a*'b\<Rightarrow>_)))  (p_var_getters p1) @
    map (\<lambda>(v, g). (v, g \<circ> embedding \<circ> snd \<circ> inv (embedding::'a*'b\<Rightarrow>_))) (p_var_getters p2)"
  unfolding p_var_getters_def pu_var_getters_def Rep_pair_pattern by simp

lemma vars_pair_pattern [simp]: "p_vars (pair_pattern p1 p2) = p_vars p1 @ p_vars p2"
    unfolding p_vars_def pu_vars_def apply (subst pu_var_getters_def) unfolding Rep_pair_pattern apply simp
    unfolding p_var_getters_def[symmetric] by auto



definition "variable_pattern (v::'a::prog_type variable) = (Abs_pattern (pattern_1var (mk_variable_untyped v)) :: 'a pattern)"
lemma Rep_variable_pattern: "Rep_pattern (variable_pattern v) = pattern_1var (mk_variable_untyped v)"
  unfolding variable_pattern_def apply (subst Abs_pattern_inverse) by auto
lemma vars_variable_pattern [simp]: "p_vars (variable_pattern v) = [mk_variable_untyped v]" 
  unfolding p_vars_def Rep_variable_pattern by simp

definition "memory_update_pattern m (v::'a pattern) (a::'a::prog_type) =
  memory_update_untyped_pattern m (Rep_pattern v) (embedding a)"

lemma memory_update_unit_pattern [simp]: "memory_update_pattern m unit_pattern x = m"
  unfolding memory_update_pattern_def memory_update_untyped_pattern_def pu_var_getters_def Rep_unit_pattern
  by simp
lemma memory_update_variable_pattern [simp]: "memory_update_pattern m (variable_pattern v) x = memory_update m v x"
  unfolding memory_update_pattern_def memory_update_untyped_pattern_def variable_pattern_def
  apply (subst Abs_pattern_inverse)
   close simp
  by (simp add: embedding_Type memory_update_def)
lemma memory_update_pair_pattern [simp]:
(*  fixes p1 p2 and m::memory and x1::"'a::prog_type" and x2::"'b::prog_type"
  shows *) "memory_update_pattern m (pair_pattern p1 p2) (x1,x2) = memory_update_pattern (memory_update_pattern m p1 x1) p2 x2"
proof -
  def p1vg == "p_var_getters p1"
  def p2vg == "p_var_getters p2"
  have tmp: "inv embedding (embedding (x1, x2)) = (x1,x2)"
    unfolding embedding_inv' ..
note [[show_types,show_sorts,show_consts]]
  have p2vg_nil: "foldl (\<lambda>m (v,f). memory_update_untyped m v (f (embedding (x1,x2)))) m
             (map (\<lambda>(v,g). (v, g \<circ> embedding \<circ> fst \<circ> inv (embedding::'a*'b\<Rightarrow>_))) p1vg) =
      (foldl (\<lambda>m (v,f). memory_update_untyped m v (f (embedding x1))) m p1vg)"
    by (induct p1vg rule:rev_induct, auto)
  have "foldl (\<lambda>m (v,f). memory_update_untyped m v (f (embedding (x1,x2)))) m
             (map (\<lambda>(v,g). (v, g \<circ> embedding \<circ> fst \<circ> inv (embedding::'a*'b\<Rightarrow>_))) p1vg @
              map (\<lambda>(v,g). (v, g \<circ> embedding \<circ> snd \<circ> inv (embedding::'a*'b\<Rightarrow>_))) p2vg) =
    foldl (\<lambda>m (v,f). memory_update_untyped m v (f (embedding x2)))
      (foldl (\<lambda>m (v,f). memory_update_untyped m v (f (embedding x1))) m p1vg) p2vg"
    apply (induct p2vg rule:rev_induct)
    using p2vg_nil unfolding embedding_inv' o_def by auto
  thus ?thesis
    unfolding memory_update_pattern_def memory_update_untyped_pattern_def p_var_getters_def[symmetric]
      var_getters_pair_pattern p1vg_def p2vg_def
    by auto
qed
lemma memory_update_pair_pattern':
  "memory_update_pattern m (pair_pattern p1 p2) x = memory_update_pattern (memory_update_pattern m p1 (fst x)) p2 (snd x)"
  by (cases x, simp)



record ('a,'b) procedure = 
  p_body :: program
  p_arg :: "'a pattern"
  p_return :: "'b expression"

definition "mk_procedure_untyped proc = 
  Proc (Rep_program (p_body proc)) (Rep_pattern (p_arg proc)) (mk_expression_untyped (p_return proc))"

fun mk_procedure_typed :: "procedure_rep \<Rightarrow> ('a::prog_type, 'b::prog_type, 'c) procedure_ext"  where
 "mk_procedure_typed (Proc body args return) = 
    \<lparr> p_body=Abs_program body, p_arg=Abs_pattern args, p_return=mk_expression_typed return, \<dots> = undefined\<rparr>"
| "mk_procedure_typed _ = undefined"

(*definition "mk_procedure args body return = \<lparr> p_body=body, p_arg=pattern_of args, p_return=return \<rparr>"*)

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
by (simp_all add: mk_procedure_untyped_def p_def procedure_type_def)

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
lemma procargvars_add_untyped [simp]: "mk_procargvars_untyped (procargvars_add x a) = mk_variable_untyped x # mk_procargvars_untyped a" 
lemma procargvars_empty_untyped [simp]: "mk_procargvars_untyped procargvars_empty = []" 
lemma procargs_add_untyped [simp]: "mk_procargs_untyped (procargs_add x a) = mk_expression_untyped x # mk_procargs_untyped a" 
lemma procargs_empty_untyped [simp]: "mk_procargs_untyped procargs_empty = []" 
lemma vars_procargs_add [simp]: "vars_procargs (procargs_add e a) = e_vars e @ vars_procargs a" 
lemma vars_procargs_empty [simp]: "vars_procargs procargs_empty = []" 
*)





subsection {* Typed programs *}

definition "label (l::string) (p::program) = p"

definition "seq p q = Abs_program (Seq (Rep_program p) (Rep_program q))"

lemma Rep_seq [simp]: "Rep_program (seq p q) = Seq (Rep_program p) (Rep_program q)"
  unfolding seq_def denotation_def apply (subst Abs_program_inverse) by auto

definition "skip = Abs_program Skip"

lemma Rep_skip [simp]: "Rep_program skip = Skip"
  unfolding skip_def denotation_def apply (subst Abs_program_inverse) by auto

definition "assign (v::('a::prog_type) pattern) (e::'a expression) =
  Abs_program (Assign (Rep_pattern v) (mk_expression_untyped e))"

lemma Rep_assign [simp]: "Rep_program (assign v e) = 
  Assign (Rep_pattern v) (mk_expression_untyped e)"
  unfolding assign_def denotation_def apply (subst Abs_program_inverse) by (simp_all)
  
definition "sample (v::('a::prog_type) pattern) (e::'a distr expression) =
  Abs_program (Sample (Rep_pattern v) (mk_expression_distr e))"

lemma Rep_sample [simp]: "Rep_program (sample v e)
   = Sample (Rep_pattern v) (mk_expression_distr e)"
  unfolding sample_def denotation_def apply (subst Abs_program_inverse) by simp_all 

definition ifte :: "bool expression \<Rightarrow> program \<Rightarrow> program \<Rightarrow> program" where
  "ifte e thn els = Abs_program (IfTE (mk_expression_untyped e) (Rep_program thn) (Rep_program els))"

lemma Rep_ifte [simp]: "Rep_program (ifte e thn els) =
  IfTE (mk_expression_untyped e) (Rep_program thn) (Rep_program els)"
  unfolding ifte_def denotation_def apply (subst Abs_program_inverse) using bool_type by auto

definition while :: "bool expression \<Rightarrow> program \<Rightarrow> program" where
  "while e p = Abs_program (While (mk_expression_untyped e) (Rep_program p))"

lemma Rep_while [simp]: "Rep_program (while e p) =
  While (mk_expression_untyped e) (Rep_program p)"
  unfolding while_def denotation_def apply (subst Abs_program_inverse) using bool_type by auto

definition callproc :: "'a::prog_type pattern \<Rightarrow> ('b::prog_type,'a) procedure \<Rightarrow> 'b expression \<Rightarrow> program" where
  "callproc v proc args = Abs_program (CallProc (Rep_pattern v) (mk_procedure_untyped proc) (mk_expression_untyped args))"
lemma Rep_callproc [simp]: "Rep_program (callproc v p a) = CallProc (Rep_pattern v) (mk_procedure_untyped p) (mk_expression_untyped a)"
  unfolding callproc_def apply (subst Abs_program_inverse)
  by (auto simp: mk_procedure_untyped_def)
  
(* lemma Rep_callproc [simp]: "Rep_program (callproc v proc args) =
  CallProc (Rep_pattern v) (mk_procedure_untyped proc) (mk_expression_untyped args)"
proof -
  have swap: "\<And>x y. list_all2 (\<lambda>(x::variable_untyped) y. vu_type x = eu_type y) x y = list_all2 (\<lambda>y x. eu_type y = vu_type x) y x"
   unfolding list_all2_conv_all_nth by auto
  show ?thesis
  unfolding callproc_def denotation_def mk_procedure_untyped_def 
  by (subst Abs_program_inverse, auto)
qed *)

(*lemma denotation_seq: "denotation (seq p q) m = 
  compose_distr (denotation_untyped (mk_program_untyped q)) (denotation_untyped (mk_program_untyped p) m)" *)
lemma denotation_seq: "denotation (seq p q) m = 
  compose_distr (denotation q) (denotation p m)"
unfolding denotation_def memory_update_def by simp

lemma denotation_skip: "denotation skip m = point_distr m"
unfolding denotation_def memory_update_def by simp

lemma denotation_assign: "denotation (assign v e) m = point_distr (memory_update_pattern m v (e_fun e m))"
  unfolding denotation_def memory_update_pattern_def by simp
lemma denotation_sample: "denotation (sample v e) m = apply_to_distr (memory_update_pattern m v) (e_fun e m)"
  unfolding denotation_def memory_update_pattern_def[THEN ext] by simp

lemma denotation_ifte: "denotation (ifte e thn els) m = (if e_fun e m then denotation thn m else denotation els m)"
  unfolding denotation_def by simp
(* TODO: define and use a typed version of While_n in the following lemma *)
lemma denotation_while: "denotation (while e p) m = 
  (SUP n. denotation_untyped (While_n n (mk_expression_untyped e) (Rep_program p)) m)"
(* Abs_distr (\<lambda>m'. \<Sum>n. Rep_distr (compose_distr (\<lambda>m. if e_fun e m then 0 else point_distr m)
                                                  (while_iter n (e_fun e) (denotation p) m)) m')" *)
  unfolding denotation_def by simp 

lemma denotation_callproc: "denotation (callproc v proc args) m =
  (let argval = e_fun args m in
  let m' = init_locals m in
  let m' = memory_update_pattern m' (p_arg proc) argval in
  apply_to_distr (\<lambda>m'.
    let res = e_fun (p_return proc) m' in
    let m' = restore_locals m m' in
    memory_update_pattern m' v res)
  (denotation (p_body proc) m'))"
  unfolding denotation_def  memory_update_pattern_def
  by (simp add: mk_procedure_untyped_def)

lemma denotation_seq_skip [simp]: "denotation (seq Lang_Typed.skip c) = denotation c"
  unfolding denotation_seq[THEN ext] denotation_def by simp 
lemma denotation_skip_seq [simp]: "denotation (seq c Lang_Typed.skip) = denotation c"
  unfolding denotation_seq[THEN ext] Rep_skip denotation_def denotation_untyped_Skip[THEN ext]
  by simp 

lemmas denotation_simp = denotation_seq denotation_skip denotation_assign denotation_sample denotation_ifte denotation_while denotation_callproc

lemma denotation_seq_assoc: "denotation (seq (seq x y) z) = denotation (seq x (seq y z))"
  unfolding denotation_seq[THEN ext] 
  unfolding compose_distr_assoc ..


subsection {* Concrete syntax for programs *}

subsubsection {* Grammar *}

nonterminal procedure_call_args_syntax
syntax "Product_Type.Unity" :: procedure_call_args_syntax ("'(')")
syntax "" :: "'a \<Rightarrow> procedure_call_args_syntax" ("'(_')")
syntax "_tuple" :: "'a \<Rightarrow> tuple_args \<Rightarrow> procedure_call_args_syntax" ("'(_,_')")

nonterminal program_syntax

syntax "_program" :: "program_syntax \<Rightarrow> term" ("PROGRAM [ _; ]")
syntax "_program" :: "program_syntax \<Rightarrow> term" ("PROGRAM [ _ ]")
syntax "_label" :: "idt \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("_: _" [10,11] 10)
syntax "_seq" :: "program_syntax \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("_;/ _" [10,11] 10)
syntax "_skip" :: "program_syntax" ("skip")
syntax "_quote" :: "program \<Rightarrow> program_syntax" ("\<guillemotleft>_\<guillemotright>" [31] 30)
syntax "_assign" :: "'a \<Rightarrow> 'b \<Rightarrow> program_syntax" (infix ":=" 30)
syntax "_sample" :: "'a \<Rightarrow> 'b \<Rightarrow> program_syntax" (infix "<-" 30)
syntax "_ifte" :: "bool \<Rightarrow> program_syntax \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("if '(_') (2_) else (2_)" [0,20] 20)
syntax "_ifthen" :: "bool \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("if '(_') (2_)" [0,20] 20)
syntax "_while" :: "bool \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("while '(_') (2_)" [0,20] 20)
syntax "_assign_quote" :: "'a variable \<Rightarrow> 'a expression \<Rightarrow> program_syntax" ("_ := \<guillemotleft>_\<guillemotright>" [31,31] 30)
syntax "_sample_quote" :: "'a variable \<Rightarrow> 'a expression \<Rightarrow> program_syntax" ("_ <- \<guillemotleft>_\<guillemotright>" [31,31] 30)
syntax "_while_quote" :: "bool expression \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("while '(\<guillemotleft>_\<guillemotright>') (2_)" [0,20] 20)
syntax "_ifte_quote" :: "bool expression \<Rightarrow> program_syntax \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("if '(\<guillemotleft>_\<guillemotright>') (2_) else _" [0,20] 20)
syntax "_ifthen_quote" :: "bool expression \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("if '(\<guillemotleft>_\<guillemotright>') (2_)" [0,20] 20)
syntax "_callproc" :: "'a \<Rightarrow> ('a,'b) procedure \<Rightarrow> procedure_call_args_syntax \<Rightarrow> program_syntax" ("_ := call _ _" 30)
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

(*
nonterminal procedure_decl_args_syntax
nonterminal procedure_decl_args_syntax'
syntax "_procedure_decl_args_none" :: procedure_decl_args_syntax ("'(')")
syntax "_procedure_decl_args_single" :: "idt \<Rightarrow> procedure_decl_args_syntax'" ("_")
syntax "_procedure_decl_args_cons" :: "idt \<Rightarrow> procedure_decl_args_syntax' \<Rightarrow> procedure_decl_args_syntax'" ("_,_")
syntax "" :: "procedure_decl_args_syntax' \<Rightarrow> procedure_decl_args_syntax" ("'(_')")
*)
syntax "_procedure_decl" :: "procedure_call_args_syntax \<Rightarrow> program_syntax \<Rightarrow> 'b \<Rightarrow> ('a,'b) procedure" ("proc _ {_; return _}")
syntax "_procedure_decl" :: "procedure_call_args_syntax \<Rightarrow> program_syntax \<Rightarrow> 'b \<Rightarrow> ('a,'b) procedure" ("proc _ {_; return _;}")

parse_translation {* [("_procedure_decl", fn ctx => fn [args,body,return] => 
let val known = Unsynchronized.ref[] (* TODO: add local vars *)
(*    fun trargs (Const(@{const_name Unity},_)) = @{term "unit_pattern"}
      | trargs (Const(@{const_syntax Pair},_)$a$b) =
          Const(@{const_name pair_pattern},dummyT) $ trargs a $ trargs b
(*          let val apat = trargs a val bpat = trargs b in
          @{termx "pair_pattern (?apat::?'apat.1) (?bpat::?'bpat.1)" 
                  where "?'apat.1\<Rightarrow>?'a pattern"   "?'bpat.1\<Rightarrow>?'b pattern"} end *)
      | trargs t = Const(@{const_name variable_pattern},dummyT) $ t*)
(* @{termx "variable_pattern (?t::?'t.1)" where "?'t.1\<Rightarrow>(?'x::prog_type variable)"} *)
(*    fun trargs (Const("_procedure_decl_args_none",_)) = Const(@{const_name TODO_REMOVE_ME},dummyT)
      | trargs (Const("_procedure_decl_args_single",_)$x) = 
          (Lang_Syntax.add_var known x; Const(@{const_name TODO_REMOVE_ME},dummyT) $ x $ Const(@{const_name TODO_REMOVE_ME},dummyT))
      | trargs (Const("_procedure_decl_args_cons",_)$x$xs) = 
          (Lang_Syntax.add_var known x; Const(@{const_name TODO_REMOVE_ME},dummyT) $ x $ trargs xs)
      | trargs t = raise (TERM ("trargs",[t])) *)
    val args = Lang_Syntax.translate_pattern known args
in
Const(@{const_name procedure_ext},dummyT) $ 
   Lang_Syntax.translate_program ctx known body $ (* p_body *)
   args $ (* p_arg *)
   Lang_Syntax.translate_expression ctx known return $ (* p_return *)
   @{term "()"}
end)] *}

lemma vars_seq [simp]: "vars (seq a b) = vars a @ vars b" by (simp add: vars_def)
lemma vars_assign [simp]: "vars (assign x e) = p_vars x @ e_vars e" by (simp add: p_vars_def vars_def)
lemma vars_sample [simp]: "vars (sample x e) = p_vars x @ e_vars e" by (simp add: p_vars_def vars_def)
lemma vars_while [simp]: "vars (Lang_Typed.while e p) = e_vars e @ vars p" by (simp add: vars_def)
lemma vars_ifte [simp]: "vars (Lang_Typed.ifte e p1 p2) = e_vars e @ vars p1 @ vars p2" by (simp add: vars_def)
definition "vars_proc_global p == [v. v<-p_vars (p_arg p), vu_global v] @ [v. v<-vars (p_body p), vu_global v] @ [v. v<-e_vars (p_return p), vu_global v]"
lemma vars_callproc [simp]: "vars (callproc x p a) = p_vars x @ e_vars a @ vars_proc_global p"
  unfolding vars_def vars_proc_global_def p_vars_def by (auto simp: mk_procedure_untyped_def)
lemma vars_skip [simp]: "vars Lang_Typed.skip = []" by (simp add: vars_def)

lemma write_vars_seq [simp]: "write_vars (seq a b) = write_vars a @ write_vars b" by (simp add: write_vars_def)
lemma write_vars_assign [simp]: "write_vars (assign x e) = p_vars x" by (simp add: p_vars_def write_vars_def)
lemma write_vars_sample [simp]: "write_vars (sample x e) = p_vars x" by (simp add: p_vars_def write_vars_def)
lemma write_vars_while [simp]: "write_vars (Lang_Typed.while e p) = write_vars p" by (simp add: write_vars_def)
lemma write_vars_ifte [simp]: "write_vars (Lang_Typed.ifte e p1 p2) = write_vars p1 @ write_vars p2" by (simp add: write_vars_def)
definition "write_vars_proc_global p == [v. v<-p_vars (p_arg p), vu_global v] @ [v. v<-write_vars (p_body p), vu_global v]"
lemma write_vars_callproc [simp]: "write_vars (callproc x p a) = p_vars x @ write_vars_proc_global p"
  unfolding write_vars_def write_vars_proc_global_def p_vars_def by (auto simp: mk_procedure_untyped_def)
lemma write_vars_skip [simp]: "write_vars Lang_Typed.skip = []" by (simp add: write_vars_def)


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

subsection {* Variable renaming *}

type_synonym variable_name_renaming = "(string * string) list"
(*definition local_variable_name_renaming :: "variable_name_renaming \<Rightarrow> variable_untyped \<Rightarrow> variable_untyped" where
  "local_variable_name_renaming ren x = 
  (if vu_global x then x
  else x \<lparr> vu_name := (fold (\<lambda>(a,b) f. Fun.swap a b f) ren id) (vu_name x) \<rparr>)"*)
definition local_variable_name_renaming1 :: "(string * string) \<Rightarrow> variable_untyped \<Rightarrow> variable_untyped" where
  "local_variable_name_renaming1 = (\<lambda>(a,b) x.
  (if vu_global x then x
  else x \<lparr> vu_name := if vu_name x = a then b else if vu_name x = b then a else vu_name x \<rparr>))"

lemma local_variable_name_renaming1_type: "vu_type (local_variable_name_renaming1 ren x) = vu_type x"
  by (cases ren, simp add: local_variable_name_renaming1_def)
lemma local_variable_name_renaming1_global: "vu_global (local_variable_name_renaming1 ren x) = vu_global x"
  by (cases ren, simp add: local_variable_name_renaming1_def)
lemma local_variable_name_renaming1_fix_globals: "vu_global x \<Longrightarrow> local_variable_name_renaming1 ren x = x"
  by (cases ren, simp add: local_variable_name_renaming1_def)
lemma local_variable_name_renaming1_bij: "bij (local_variable_name_renaming1 ren)"
proof -
  obtain a b where ren:"ren = (a,b)" by (cases ren, simp)
  have "local_variable_name_renaming1 ren o local_variable_name_renaming1 ren = id"
    unfolding ren id_def o_def local_variable_name_renaming1_def by auto
  thus "bij (local_variable_name_renaming1 ren)"
    using o_bij by blast
qed

definition local_variable_name_renaming :: "variable_name_renaming \<Rightarrow> variable_untyped \<Rightarrow> variable_untyped" where
  "local_variable_name_renaming ren = fold local_variable_name_renaming1 ren"
(*lemma local_variable_name_renaming1:
  "local_variable_name_renaming ren x = fold local_variable_name_renaming1 ren x"
proof (induct ren)
  show "local_variable_name_renaming [] x = fold local_variable_name_renaming1 [] x"
    unfolding local_variable_name_renaming_def local_variable_name_renaming1_def by simp
next
  fix ab::"string * string" and ren obtain a b where ab: "ab=(a,b)" by (cases ab, simp)
  assume ih: "local_variable_name_renaming ren x = fold local_variable_name_renaming1 ren x"
  show "local_variable_name_renaming (ab # ren) x = fold local_variable_name_renaming1 (ab # ren) x"
  proof (cases "vu_global x")
    assume "vu_global x"
    have "local_variable_name_renaming (ab # ren) x = x"
      by (simp add: `vu_global x` local_variable_name_renaming_def)
    also have "local_variable_name_renaming ren x = x"
      by (simp add: `vu_global x` local_variable_name_renaming_def)
    hence "fold local_variable_name_renaming1 (ab # ren) x = x"
      apply simp apply (subst (2) local_variable_name_renaming1_def) unfolding ab using `vu_global x` ih by auto
    ultimately show "local_variable_name_renaming (ab # ren) x = fold local_variable_name_renaming1 (ab # ren) x"
      by simp
  next
    assume "\<not> vu_global x"
    have swap: "(Fun.swap a b id) (vu_name x) = (if vu_name x = a then b else if vu_name x = b then a else vu_name x)"
      by auto
    have "local_variable_name_renaming (ab # ren) x = undefined"
      unfolding local_variable_name_renaming_def apply (simp add: `\<not> vu_global x` ab swap)
    show "local_variable_name_renaming (ab # ren) x = fold local_variable_name_renaming1 (ab # ren) x"
      by later
  qed
qed*)


lemma local_variable_name_renaming_type [simp]: "vu_type (local_variable_name_renaming ren x) = vu_type x"
  unfolding local_variable_name_renaming_def apply (induct ren rule:rev_induct)
  using local_variable_name_renaming1_type by auto
lemma local_variable_name_renaming_global [simp]: "vu_global (local_variable_name_renaming ren x) = vu_global x"
  unfolding local_variable_name_renaming_def apply (induct ren rule:rev_induct)
  using local_variable_name_renaming1_global by auto
lemma local_variable_name_renaming_fix_globals: "vu_global x \<Longrightarrow> local_variable_name_renaming ren x = x"
  unfolding local_variable_name_renaming_def apply (induct ren rule:rev_induct)
  using local_variable_name_renaming1_fix_globals by auto

lemma local_variable_name_renaming_bij: "bij (local_variable_name_renaming ren)"
  unfolding local_variable_name_renaming_def
  apply (induct ren rule:rev_induct)
  using o_bij close force
  apply simp unfolding o_def[symmetric]
  by (simp add: bij_comp local_variable_name_renaming1_bij)


definition rename_local_variables :: "variable_name_renaming \<Rightarrow> program \<Rightarrow> program" where
  "rename_local_variables ren p = Abs_program (rename_variables 
      (local_variable_name_renaming ren) (Rep_program p))"
lemma Rep_rename_local_variables [simp]: "Rep_program (rename_local_variables ren p) =
  rename_variables (local_variable_name_renaming ren) (Rep_program p)"
      unfolding rename_local_variables_def
      apply (subst Abs_program_inverse, auto)
      by (simp add: well_typed_rename_variables) 

definition rename_local_variables_expression :: "variable_name_renaming \<Rightarrow> 'a::prog_type expression \<Rightarrow> 'a expression" where
  "rename_local_variables_expression ren e = mk_expression_typed (rename_variables_expression 
      (local_variable_name_renaming ren) (mk_expression_untyped e))"
lemma Rep_rename_local_variables_expression [simp]: "mk_expression_untyped (rename_local_variables_expression ren e) =
  rename_variables_expression (local_variable_name_renaming ren) (mk_expression_untyped e)"
      unfolding rename_local_variables_expression_def
      apply (subst mk_expression_typed_inverse)
      by (simp_all add: eu_type_rename_variables)
lemma e_fun_rename_local_variables_expression [simp]: "e_fun (rename_local_variables_expression ren e) = 
    (e_fun e) o (rename_variables_memory (local_variable_name_renaming ren))"
  unfolding e_fun_eu_fun eu_fun_def o_def by simp

lemma rename_local_variables_expression_id [simp]: "rename_local_variables_expression [] e = e"
proof -
  have upd: "\<And>x. x \<lparr> vu_name := vu_name x \<rparr> = x" by (case_tac x, auto)
  show ?thesis
    unfolding rename_local_variables_expression_def local_variable_name_renaming_def[THEN ext] fold_Nil id_def upd
    using rename_variables_expression_id[unfolded id_def]
    apply auto by (rule mk_expression_untyped_inverse)
qed





lemma Rep_rename_local_variables_expression_distr [simp]: "mk_expression_distr (rename_local_variables_expression ren e) =
  rename_variables_expression_distr (local_variable_name_renaming ren) (mk_expression_distr e)"
proof -
  have vars: "eu_vars (rename_variables_expression (local_variable_name_renaming ren) (mk_expression_untyped e)) =
    map (local_variable_name_renaming ren) (e_vars e)"
    apply (subst eu_vars_rename_variables_expression) by simp_all
  have fn: "(\<lambda>x\<Colon>val. apply_to_distr embedding (inv embedding x :: 'a distr)) \<circ>
    eu_fun (rename_variables_expression (local_variable_name_renaming ren) (mk_expression_untyped e)) =
    (\<lambda>m\<Colon>memory. apply_to_distr (embedding::'a\<Rightarrow>_) (e_fun e (rename_variables_memory (local_variable_name_renaming ren) m)))"
    apply (subst eu_fun_rename_variables_expression)
    unfolding mk_expression_untyped_fun[THEN ext] o_def by simp_all
  show ?thesis
    unfolding rename_local_variables_expression_def 
    apply (rule Rep_expression_distr_inject[THEN iffD1])
    apply (subst mk_expression_distr_mk_expression_typed)
     close (metis Rep_rename_local_variables_expression mk_expression_untyped_type)
    apply (subst Rep_rename_variables_expression_distr)
      close simp close simp
      using fn vars by auto
qed

definition rename_local_variables_pattern :: "variable_name_renaming \<Rightarrow> 'a::prog_type pattern \<Rightarrow> 'a pattern" where
  "rename_local_variables_pattern ren p = Abs_pattern (rename_variables_pattern
      (local_variable_name_renaming ren) (Rep_pattern p))"
lemma Rep_rename_local_variables_pattern [simp]: "Rep_pattern (rename_local_variables_pattern ren p) =
        rename_variables_pattern (local_variable_name_renaming ren) (Rep_pattern p)"
  unfolding rename_local_variables_pattern_def
  apply (subst Abs_pattern_inverse)
  by (simp_all add: pu_type_rename_variables)


lemma rename_variables_pattern_id: "rename_variables_pattern id p = p" 
  apply (induct p)
  by (auto simp: id_def rename_variables_pattern_id[unfolded id_def])

lemma p_vars_rename_local_variables_pattern: "p_vars (rename_local_variables_pattern ren p) = 
  map (local_variable_name_renaming ren) (p_vars p)"
unfolding p_vars_def Rep_rename_local_variables_pattern
by (subst pu_vars_rename_variables_pattern, simp_all)

lemma rename_local_variables_pair_pattern [simp]: 
  "rename_local_variables_pattern R (pair_pattern p1 p2)
  = pair_pattern (rename_local_variables_pattern R p1) (rename_local_variables_pattern R p2)"
  apply (rule Rep_pattern_inject[THEN iffD1])
  apply (subst Rep_rename_local_variables_pattern)
  apply (rule Rep_pattern_untyped_inject[THEN iffD1])
  apply (subst Rep_pair_pattern)
  apply (subst Rep_rename_variables_pattern) close simp
  apply (subst pu_var_getters_def)
  apply (subst Rep_pair_pattern)
  apply auto
  unfolding p_var_getters_def
  apply (subst Rep_rename_local_variables_pattern)+
  apply (subst pu_var_getters_rename_variables_pattern[OF local_variable_name_renaming_type])+
  unfolding apfst_def map_prod_def id_def
  by auto  

lemma e_vars_rename_local_variables_expression [simp]: "e_vars (rename_local_variables_expression ren e) = 
  map (local_variable_name_renaming ren) (e_vars e)"
unfolding mk_expression_untyped_vars[symmetric] Rep_rename_local_variables_expression
by (subst eu_vars_rename_variables_expression, simp_all)

definition rename_local_variables_var :: "variable_name_renaming \<Rightarrow> 'a::prog_type variable \<Rightarrow> 'a::prog_type variable" where
  "rename_local_variables_var ren v = mk_variable_typed (local_variable_name_renaming ren (mk_variable_untyped v))"
lemma Rep_rename_local_variables_var [simp]: "mk_variable_untyped (rename_local_variables_var ren v) 
        = local_variable_name_renaming ren (mk_variable_untyped v)"
  unfolding rename_local_variables_var_def
  apply (subst mk_variable_typed_inverse)
  by simp_all

lemma rename_local_variables_var_id [simp]: "rename_local_variables_var [] x = x"
proof -
  show ?thesis
    unfolding rename_local_variables_var_def local_variable_name_renaming_def[THEN ext] 
    by auto
qed

abbreviation rename_local_variables_memory :: "variable_name_renaming \<Rightarrow> memory \<Rightarrow> memory" where
  "rename_local_variables_memory ren == rename_variables_memory (local_variable_name_renaming ren)"


lemma lookup_rename_local_variables_memory [simp]: 
  shows "memory_lookup (rename_local_variables_memory ren m) v = memory_lookup m (rename_local_variables_var ren v)"
by (simp add: Rep_rename_variables_memory memory_lookup_def)
  

definition rename_local_variables_proc :: "variable_name_renaming \<Rightarrow> ('a::prog_type,'b::prog_type)procedure \<Rightarrow> ('a,'b)procedure" where
  "rename_local_variables_proc ren p = mk_procedure_typed (rename_variables_proc 
      (local_variable_name_renaming ren) (mk_procedure_untyped p))"
lemma Rep_rename_local_variables_proc: "mk_procedure_untyped (rename_local_variables_proc ren p) = 
  rename_variables_proc (local_variable_name_renaming ren) (mk_procedure_untyped p)"
proof -
  obtain body pargs ret where p: "mk_procedure_untyped p = Proc body pargs ret" 
      and pu_type_pargs: "pu_type pargs = Type TYPE('a)" and eu_type_ret: "eu_type ret = Type TYPE('b)" 
      and wt_body: "well_typed body"
    by (simp add: mk_procedure_untyped_def) 
  def f == "(local_variable_name_renaming ren)"
  def body' == "rename_variables f body"
  def pargs' == "rename_variables_pattern f pargs"
  def ret' == "rename_variables_expression f ret"
  have type: "\<And>x. vu_type (f x) = vu_type x" unfolding f_def by simp
  have global: "\<And>x. vu_global (f x) = vu_global x" unfolding f_def by simp
  have wt_body': "well_typed body'"
    unfolding body'_def apply (rule well_typed_rename_variables)
    close (fact type) close (fact global) by (fact wt_body)
  have pu_type_pargs': "pu_type pargs' = Type TYPE('a)"
    unfolding pu_type_def pargs'_def Rep_rename_variables_pattern[OF type]
    apply simp unfolding pu_type_def[symmetric] pu_type_pargs ..
  have eu_type_ret': "eu_type ret' = Type TYPE('b)"
    unfolding ret'_def eu_type_def Rep_rename_variables_expression[OF type global]
    apply simp unfolding eu_type_def[symmetric] eu_type_ret ..
  have p': "rename_variables_proc (local_variable_name_renaming ren) (mk_procedure_untyped p) = Proc body' pargs' ret'"
    unfolding p f_def body'_def pargs'_def ret'_def by simp
  show ?thesis
    unfolding rename_local_variables_proc_def p' 
    apply (subst mk_procedure_typed_inverse[OF wt_body' pu_type_pargs' eu_type_ret'])..
qed

lemma p_body_rename_local_variables_proc: 
  shows "p_body (rename_local_variables_proc ren p) = rename_local_variables ren (p_body p)"
proof -
  obtain body' pargs' ret' where as_Proc: "mk_procedure_untyped (rename_local_variables_proc ren p) = Proc body' pargs' ret'"
      and rename: "Proc body' pargs' ret' = rename_variables_proc (local_variable_name_renaming ren) (mk_procedure_untyped p)"
    by (metis Rep_rename_local_variables_proc mk_procedure_untyped_def)
  have p_body: "p_body (rename_local_variables_proc ren p) = Abs_program body'"
    by (metis as_Proc mk_procedure_typed.simps(1) mk_procedure_untyped_inverse procedure.ext_inject procedure.surjective)
  have "body' = rename_variables (local_variable_name_renaming ren) (Rep_program (p_body p))"
    using rename unfolding mk_procedure_untyped_def by auto
  hence "Abs_program body' = rename_local_variables ren (p_body p)"
    by (simp add: rename_local_variables_def)
  with p_body show ?thesis by simp
qed

lemma p_arg_rename_local_variables_proc: 
  shows "p_arg (rename_local_variables_proc ren p) = rename_local_variables_pattern ren (p_arg p)"
proof -
  obtain body' pargs' ret' where as_Proc: "mk_procedure_untyped (rename_local_variables_proc ren p) = Proc body' pargs' ret'"
      and rename: "Proc body' pargs' ret' = rename_variables_proc (local_variable_name_renaming ren) (mk_procedure_untyped p)"
    by (metis Rep_rename_local_variables_proc mk_procedure_untyped_def)
  have p_arg: "p_arg (rename_local_variables_proc ren p) = Abs_pattern pargs'"
    by (metis as_Proc mk_procedure_typed.simps(1) mk_procedure_untyped_inverse procedure.select_convs(2))
  have "pargs' = rename_variables_pattern (local_variable_name_renaming ren) (Rep_pattern (p_arg p))"
    using rename unfolding mk_procedure_untyped_def by auto
  hence "Abs_pattern pargs' = rename_local_variables_pattern ren (p_arg p)"
    by (simp add: rename_local_variables_pattern_def)
  with p_arg show ?thesis by simp
qed

lemma p_ret_rename_local_variables_proc: 
  shows "p_return (rename_local_variables_proc ren p) = rename_local_variables_expression ren (p_return p)"
proof -
  obtain body' pargs' ret' where as_Proc: "mk_procedure_untyped (rename_local_variables_proc ren p) = Proc body' pargs' ret'"
      and rename: "Proc body' pargs' ret' = rename_variables_proc (local_variable_name_renaming ren) (mk_procedure_untyped p)"
    by (metis Rep_rename_local_variables_proc mk_procedure_untyped_def)
  have p_ret: "p_return (rename_local_variables_proc ren p) = mk_expression_typed ret'"
    by (metis mk_procedure_typed.simps(1) procedure.select_convs(3) rename rename_local_variables_proc_def)
  have "ret' = rename_variables_expression (local_variable_name_renaming ren) (mk_expression_untyped (p_return p))"
    using rename unfolding mk_procedure_untyped_def by auto
  hence "mk_expression_typed ret' = rename_local_variables_expression ren (p_return p)"
    by (simp add: rename_local_variables_expression_def)
  with p_ret show ?thesis by simp
qed


lemma denotation_callproc_rename_local_variables_proc: "denotation (callproc x (rename_local_variables_proc ren p) a) = denotation (callproc x p a)"
proof -
  def f == "local_variable_name_renaming ren"
  (* def x' == "mk_pattern_untyped x" *)
  (* def a' == "mk_expression_untyped a" *)
  have type: "\<And>x. vu_type (f x) = vu_type x" unfolding f_def by simp
  have global: "\<And>x. vu_global (f x) = vu_global x" unfolding f_def by simp
  have fix_global: "\<And>x. vu_global x \<Longrightarrow> f x = x" unfolding f_def by (rule local_variable_name_renaming_fix_globals)
  have "bij f" unfolding f_def by (fact local_variable_name_renaming_bij)
  show ?thesis
    unfolding denotation_def Rep_callproc (* x'_def[symmetric] a'_def[symmetric] *)
    unfolding Rep_rename_local_variables_proc f_def[symmetric]
    by (subst denotation_rename_variables_proc[OF type global fix_global `bij f`], simp_all)
qed

lemma rename_local_variables_proc_id [simp]: "rename_local_variables_proc [] p = p"
proof -
  have upd: "\<And>x. x \<lparr> vu_name := vu_name x \<rparr> = x" by (case_tac x, auto)
  show ?thesis
    unfolding rename_local_variables_proc_def local_variable_name_renaming_def[THEN ext] fold_Nil id_def upd
    using rename_variables_proc_id[unfolded id_def]
    apply auto by (rule mk_procedure_untyped_inverse)
qed

lemma vars_rename_local_variables: "vars (rename_local_variables ren p)
                           = map (local_variable_name_renaming ren) (vars p)"
proof -
  def p' == "Rep_program p"
  have pu_vars: "\<And>x. pu_vars (rename_variables_pattern (local_variable_name_renaming ren) x) =
                map (local_variable_name_renaming ren) (pu_vars x)"
    unfolding Rep_rename_local_variables_pattern
    by (subst pu_vars_rename_variables_pattern, simp_all)
  have eu_vars: "\<And>x. eu_vars (rename_variables_expression (local_variable_name_renaming ren) x) =
       map (local_variable_name_renaming ren) (eu_vars x)"
    unfolding Rep_rename_local_variables_expression
    by (subst eu_vars_rename_variables_expression, simp_all)
  have ed_vars: "\<And>x. ed_vars (rename_variables_expression_distr (local_variable_name_renaming ren) x) =
       map (local_variable_name_renaming ren) (ed_vars x)"
    unfolding Rep_rename_local_variables_expression_distr
    by (subst ed_vars_rename_variables_expression_distr, simp_all)
  have proc_vars: "\<And>q. map (local_variable_name_renaming ren) (vars_proc_untyped q) = vars_proc_untyped q"
    by (simp add: vars_proc_untyped_global local_variable_name_renaming_fix_globals map_idI)
  def q == "undefined :: procedure_rep"
  have "vars_untyped (rename_variables (local_variable_name_renaming ren) p') 
      = map (local_variable_name_renaming ren) (vars_untyped p')"
    and True
    apply (induct p' and q)
    by (auto simp: eu_vars pu_vars ed_vars proc_vars)
  thus ?thesis
    unfolding vars_def Rep_rename_local_variables p'_def by simp
qed
  
lemma local_vars_rename_local_variables: "local_vars (rename_local_variables ren p)
                            = map (local_variable_name_renaming ren) (local_vars p)"
  unfolding local_vars_def vars_rename_local_variables
  by (metis (mono_tags, lifting) comp_apply filter_cong filter_map local_variable_name_renaming_global)


lemma rename_local_variables_pattern_id [simp]: "rename_local_variables_pattern [] p = p"
proof -
  have upd: "\<And>x. x \<lparr> vu_name := vu_name x \<rparr> = x" by (case_tac x, auto)
  show ?thesis
    unfolding rename_local_variables_pattern_def local_variable_name_renaming_def[THEN ext] fold_Nil id_def upd
    using rename_variables_pattern_id[unfolded id_def]
    apply auto by (rule Rep_pattern_inverse)
qed

lemma rename_local_variables_id [simp]: "rename_local_variables [] p = p"
proof -
  have upd: "\<And>x. x \<lparr> vu_name := vu_name x \<rparr> = x" by (case_tac x, auto)
  show ?thesis
    unfolding rename_local_variables_def local_variable_name_renaming_def[THEN ext] fold_Nil id_def upd
    using rename_variables_id[unfolded id_def]
    apply auto by (rule Rep_program_inverse)
qed



lemma rename_local_variables_unit_pattern [simp]: "rename_local_variables_pattern ren unit_pattern = unit_pattern"
  apply (rule Rep_pattern_inject[THEN iffD1])
  apply (subst Rep_rename_local_variables_pattern)
  apply (rule Rep_pattern_untyped_inject[THEN iffD1])
  apply (subst Rep_rename_variables_pattern[OF local_variable_name_renaming_type])
  unfolding pu_var_getters_def
  apply (subst Rep_unit_pattern)+
  by simp

lemma rename_local_variables_variable_pattern [simp]: "rename_local_variables_pattern ren (variable_pattern v) = variable_pattern (rename_local_variables_var ren v)"
  apply (rule Rep_pattern_inject[THEN iffD1])
  apply (subst Rep_rename_local_variables_pattern)
  apply (rule Rep_pattern_untyped_inject[THEN iffD1])
  apply (subst Rep_rename_variables_pattern[OF local_variable_name_renaming_type])
  unfolding pu_var_getters_def
  apply (subst Rep_variable_pattern)+
  apply (subst Rep_pattern_1var)+
  by auto

lemma rename_local_variables_sample [simp]: "rename_local_variables ren (sample x e) = sample (rename_local_variables_pattern ren x) (rename_local_variables_expression ren e)"
  apply (rule Rep_program_inject[THEN iffD1]) by auto

lemma rename_local_variables_skip [simp]: "rename_local_variables ren Lang_Typed.skip = Lang_Typed.skip"
  apply (rule Rep_program_inject[THEN iffD1]) by auto

lemma rename_local_variables_callproc [simp]: "rename_local_variables ren (callproc x p e) = 
  callproc (rename_local_variables_pattern ren x) p (rename_local_variables_expression ren e)"
  apply (rule Rep_program_inject[THEN iffD1]) by auto

lemma rename_local_variables_assign [simp]: "rename_local_variables ren (assign x e) = assign (rename_local_variables_pattern ren x) (rename_local_variables_expression ren e)"
  apply (rule Rep_program_inject[THEN iffD1]) by auto

lemma rename_local_variables_seq [simp]: "rename_local_variables ren (seq p1 p2) = seq (rename_local_variables ren p1) (rename_local_variables ren p2)"
  apply (rule Rep_program_inject[THEN iffD1]) by auto

lemma rename_local_variables_ifte [simp]: "rename_local_variables ren (ifte e p1 p2) = ifte (rename_local_variables_expression ren e) (rename_local_variables ren p1) (rename_local_variables ren p2)"
  apply (rule Rep_program_inject[THEN iffD1]) by auto

lemma rename_local_variables_while [simp]: "rename_local_variables ren (Lang_Typed.while e p1) = Lang_Typed.while (rename_local_variables_expression ren e) (rename_local_variables ren p1)"
  apply (rule Rep_program_inject[THEN iffD1]) by auto

lemma rename_local_variables_apply_expression [simp]: "rename_local_variables_expression ren (apply_expression e v)
     = apply_expression (rename_local_variables_expression ren e) (rename_local_variables_var ren v)"
  apply (rule mk_expression_untyped_inject[THEN iffD1]) 
  apply (rule Rep_expression_untyped_inject[THEN iffD1])
  by auto

lemma rename_local_variables_var_same [simp]: "rename_local_variables_var ((n,m)#X) (LVariable n) = rename_local_variables_var X (LVariable m)"
  apply (rule mk_variable_untyped_inject[THEN iffD1], simp)
  unfolding local_variable_name_renaming_def apply simp
  unfolding local_variable_name_renaming1_def 
  by (simp add: mk_variable_untyped_def)

lemma rename_local_variables_var_notsame [simp]: "n\<noteq>x \<Longrightarrow> m\<noteq>x \<Longrightarrow> rename_local_variables_var ((n,m)#X) (LVariable x) = rename_local_variables_var X (LVariable x)"
  apply (rule mk_variable_untyped_inject[THEN iffD1], simp)
  unfolding local_variable_name_renaming_def apply simp
  unfolding local_variable_name_renaming1_def 
  by (simp add: mk_variable_untyped_def)

lemma rename_local_variables_var_global [simp]: "rename_local_variables_var X (Variable x) = Variable x"
  apply (rule mk_variable_untyped_inject[THEN iffD1], simp)
  unfolding local_variable_name_renaming_def
  apply (induct X, simp)
  unfolding local_variable_name_renaming1_def by auto


lemma rename_local_variables_const_expression [simp]:
  "rename_local_variables_expression X (const_expression e) = const_expression e"
  apply (rule mk_expression_untyped_inject[THEN iffD1]) 
  apply (rule Rep_expression_untyped_inject[THEN iffD1])
  by auto

subsection {* Misc *}

thm while_unfold_untyped

lemma while_unfold: "denotation (Lang_Typed.while e p) = denotation (ifte e (seq p (Lang_Typed.while e p)) Lang_Typed.skip)"
  unfolding denotation_def using while_unfold_untyped by simp 



end
