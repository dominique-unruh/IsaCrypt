theory Lang_Untyped
imports Main Orderings Series Distr Universe 
begin

subsection {* Types *}

record type_rep = 
  tr_domain :: "val set"
  tr_default :: "val"
typedef type = "{(t::type_rep). tr_default t \<in> tr_domain t}"
  by (metis CollectI UNIV_I select_convs(1))
definition t_domain :: "type \<Rightarrow> val set" where
  "t_domain t = tr_domain (Rep_type t)"
definition t_default :: "type \<Rightarrow> val" where
  "t_default t = tr_default (Rep_type t)"
lemma [simp]: "t_default t \<in> t_domain t"
  unfolding t_domain_def t_default_def using Rep_type ..
type_synonym variable_name = string

subsection {* Variables *}

record variable_untyped = 
  vu_name::variable_name
  vu_type::type
  vu_global::bool

definition "bool_type =
      Abs_type \<lparr> tr_domain=range (embedding::bool\<Rightarrow>val),
                 tr_default=embedding (default::bool) \<rparr>"
definition "unit_type =
      Abs_type \<lparr> tr_domain=range (embedding::unit\<Rightarrow>val),
                 tr_default=embedding (default::unit) \<rparr>"
lemma Rep_unit_type: "Rep_type unit_type = \<lparr> tr_domain=range (embedding::unit\<Rightarrow>val),
                                             tr_default=embedding () \<rparr>"
  unfolding unit_type_def apply (subst Abs_type_inverse) by auto
lemma t_domain_unit [simp]: "t_domain unit_type = {embedding ()}"
  unfolding t_domain_def Rep_unit_type by auto
lemma t_default_unit [simp]: "t_default unit_type = embedding ()"
  unfolding t_default_def Rep_unit_type by auto
definition "prod_type T1 T2 = 
      Abs_type \<lparr> tr_domain = val_prod_embedding ` (t_domain T1 \<times> t_domain T2),
                 tr_default = val_prod_embedding (t_default T1, t_default T2) \<rparr>"
lemma Rep_prod_type: "Rep_type (prod_type T1 T2)
            = \<lparr>tr_domain = val_prod_embedding ` (t_domain T1 \<times> t_domain T2),
               tr_default = val_prod_embedding (t_default T1, t_default T2)\<rparr>"
    unfolding prod_type_def apply (subst Abs_type_inverse) by auto

lemma t_domain_prod [simp]: "t_domain (prod_type T1 T2) = val_prod_embedding ` (t_domain T1 \<times> t_domain T2)" (is ?domain)
  and t_default_prod [simp]: "t_default (prod_type T1 T2) = val_prod_embedding (t_default T1, t_default T2)" (is ?default)
unfolding t_domain_def t_default_def Rep_prod_type by auto

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

fun fresh_variables_local :: "variable_untyped list \<Rightarrow> type list \<Rightarrow> variable_untyped list" where
  "fresh_variables_local used [] = []"
| "fresh_variables_local used (t#ts) =
    (let vn=freshvar used in 
     let v=\<lparr> vu_name=vn, vu_type=t, vu_global=False \<rparr> in
     v#fresh_variables_local (v#used) ts)"
lemma fresh_variables_local_distinct: "distinct (fresh_variables_local used ts)"
proof -
  have "distinct (fresh_variables_local used ts) \<and> (\<forall>x\<in>set used. x\<notin>set (fresh_variables_local used ts))"
  proof (induction ts arbitrary: used)
  case Nil show ?case by simp
  case (Cons t ts) 
    define vn v vs where "vn == freshvar used"
      and "v == \<lparr> vu_name=vn, vu_type=t, vu_global=False \<rparr>"
      and "vs == fresh_variables_local (v#used) ts"
    have v_vs: "fresh_variables_local used (t#ts) = v#vs"
      unfolding vs_def v_def vn_def by (auto simp: Let_def)
    from Cons.IH vs_def have vs_dist: "distinct vs" by auto
    from Cons.IH vs_def have unused: "\<forall>x\<in>set (v#used). x\<notin>set vs" by blast
    hence vfresh: "v\<notin>set vs" by auto
    from vfresh vs_dist have vvs_dist: "distinct (v#vs)" by auto
    have vunused: "v \<notin> set used"
      unfolding v_def vn_def using freshvar_def2[where vs=used] by auto
    have "\<forall>x\<in>set used. x \<notin> set (v#vs)" using unused vunused by auto
    with vvs_dist show ?case unfolding v_vs by simp
  qed
  thus ?thesis by simp
qed

lemma fresh_variables_local_local: "\<forall>v\<in>set (fresh_variables_local used ts). \<not> vu_global v"
  apply (induction ts arbitrary: used, auto)
  by (metis (poly_guards_query) set_ConsD variable_untyped.select_convs(3)) 
lemma fresh_variables_local_type: "map vu_type (fresh_variables_local used ts) = ts"
  apply (induction ts arbitrary: used, auto)
  by (metis list.simps(9) variable_untyped.select_convs(2))
  

subsection {* Memories *}

(*
record memory_rep = 
  mem_globals :: "variable_untyped \<Rightarrow> val"
  mem_locals :: "variable_untyped \<Rightarrow> val"
(*  mem_stack :: "(variable_untyped \<Rightarrow> val) list" *)
*)

typedef memory = "{m::variable_untyped \<Rightarrow> val. (\<forall>v. m v \<in> t_domain (vu_type v))}"
  by (rule exI[of _ "(\<lambda>v. t_default (vu_type v))"], simp)
(*   \<and> (\<forall>v. mem_locals m v \<in> t_domain (vu_type v))e ve
(*   \<and> (\<forall>s\<in>set (mem_stack m). \<forall>v. s v \<in> t_domain (vu_type v))*)}"*)
(*apply (rule exI[where x="\<lparr> mem_globals = (\<lambda>v. t_default (vu_type v)),
                           mem_locals = (\<lambda>v. t_default (vu_type v)) \<rparr>"])
  by auto*)

(*
typedef memory = "{(m::variable_untyped\<Rightarrow>val). (\<forall>v. m v \<in> t_domain (vu_type v))}"
  apply (rule exI[of _ "\<lambda>v. t_default (vu_type v)"], simp);
  by (metis Rep_type mem_Collect_eq t_default_def t_domain_def)
*)

abbreviation "memory_lookup_untyped m v \<equiv> Rep_memory m v"
lemma memory_lookup_untyped_type [simp]: "memory_lookup_untyped m v \<in> t_domain (vu_type v)"
  using Rep_memory by auto


lemma memory_lookup_untyped_inject: "memory_lookup_untyped m = memory_lookup_untyped m' \<Longrightarrow> m=m'"
  apply (cases m, cases m', simp)
  apply (subst (asm) Abs_memory_inverse) close simp
  apply (subst (asm) Abs_memory_inverse) close simp
  by simp

definition "memory_update_untyped m v x = 
    Abs_memory ((Rep_memory m)(v:=if x\<in>t_domain(vu_type v) then x else t_default(vu_type v)))"

lemma Rep_memory_update_untyped': "Rep_memory (memory_update_untyped m v x) 
        = ((Rep_memory m)(v:=if x\<in>t_domain(vu_type v) then x else t_default(vu_type v)))"
  unfolding memory_update_untyped_def apply (subst Abs_memory_inverse)
  using Rep_memory by auto

lemma Rep_memory_update_untyped:
  assumes "v \<in> t_domain (vu_type x)" 
  shows "Rep_memory (memory_update_untyped m x v) = (Rep_memory m)(x := v)"
  unfolding memory_update_untyped_def apply (subst Abs_memory_inverse)
  using Rep_memory assms by auto

lemma memory_lookup_update_same_untyped: "a \<in> t_domain (vu_type v) \<Longrightarrow> memory_lookup_untyped (memory_update_untyped m v a) v = a"
  unfolding memory_update_untyped_def 
  apply auto
  by (subst Abs_memory_inverse, auto)


lemma memory_lookup_update_notsame_untyped: 
  "v \<noteq> w \<Longrightarrow> memory_lookup_untyped (memory_update_untyped m v a) w = memory_lookup_untyped m w"
  unfolding memory_update_untyped_def 
  apply auto
  apply (subst Abs_memory_inverse, auto)
  using Rep_memory Abs_memory_inverse Rep_type t_default_def t_domain_def by auto
  
lemma memory_lookup_update_untyped: "memory_lookup_untyped (memory_update_untyped m v a) w = 
  (if v=w then (if a \<in> t_domain (vu_type v) then a else t_default (vu_type v)) else memory_lookup_untyped m w)"
  apply (cases "v=w")
  apply (cases "a \<in> t_domain (vu_type v)")
  using memory_lookup_update_same_untyped close auto
  defer
  using memory_lookup_update_notsame_untyped close auto
  unfolding memory_update_untyped_def Let_def
  using Abs_memory_inverse Rep_memory Rep_type t_default_def t_domain_def by auto

lemma memory_update_lookup_untyped [simp]: "memory_update_untyped m x (memory_lookup_untyped m x) = m"
  apply (rule Rep_memory_inject[THEN iffD1])
  apply (subst Rep_memory_update_untyped)
  using memory_lookup_untyped_type close auto
  by auto


lemma memory_update_untyped_twice_notsame: 
  assumes "x \<noteq> y"
  shows "memory_update_untyped (memory_update_untyped m x xv) y yv
       = memory_update_untyped (memory_update_untyped m y yv) x xv"
apply (subst Rep_memory_inject[symmetric], rule ext)
apply (subst Rep_memory_update_untyped')+
using assms by auto

lemma memory_update_untyped_twice_same [simp]: 
  shows "memory_update_untyped (memory_update_untyped m x xv) x yv
       = memory_update_untyped m x yv"
apply (subst Rep_memory_inject[symmetric], rule ext)
apply (subst Rep_memory_update_untyped')+
by auto



instantiation memory :: default begin
definition "default = Abs_memory (\<lambda>x. t_default (vu_type x))"
instance ..
end
lemma Rep_memory_default [simp]: "Rep_memory default = (\<lambda>x. t_default (vu_type x))"
  unfolding default_memory_def apply (subst Abs_memory_inverse) by auto

definition "memory_combine X m1 m2 = Abs_memory (\<lambda>x. if x\<in>X then Rep_memory m1 x else Rep_memory m2 x)"
lemma Rep_memory_combine [simp]: "Rep_memory (memory_combine X m1 m2) = (\<lambda>x. if x\<in>X then Rep_memory m1 x else Rep_memory m2 x)"
  unfolding memory_combine_def apply (subst Abs_memory_inverse) using Rep_memory by auto

lemma memory_combine_twice_right [simp]:
  "memory_combine X m1 (memory_combine X m2 m3) = memory_combine X m1 m3"
  unfolding Rep_memory_inject[symmetric] by auto
lemma memory_combine_twice_left [simp]:
  "memory_combine X (memory_combine X m1 m2) m3 = memory_combine X m1 m3"
  unfolding Rep_memory_inject[symmetric] by auto

lemma memory_update_untyped_footprint: (* TODO replace by stronger one below *)
  assumes "\<And>v. v\<in>X \<Longrightarrow> memory_lookup_untyped m1 v = memory_lookup_untyped m2 v"
  assumes "w \<in> X"
  shows   "\<And>v. v\<in>X \<Longrightarrow> memory_lookup_untyped (memory_update_untyped m1 w x) v = memory_lookup_untyped (memory_update_untyped m2 w x) v"
by (simp add: assms(1) memory_lookup_update_untyped)

lemma memory_update_untyped_footprint_STRONGER:
  assumes "\<And>v. v\<in>X \<Longrightarrow> memory_lookup_untyped m1 v = memory_lookup_untyped m2 v"
  shows   "\<And>v. v\<in>X \<Longrightarrow> memory_lookup_untyped (memory_update_untyped m1 w x) v = memory_lookup_untyped (memory_update_untyped m2 w x) v"
by (simp add: assms(1) memory_lookup_update_untyped)


subsection {* Expressions *}

record expression_untyped_rep =
  eur_fun :: "memory \<Rightarrow> val"
  eur_type :: type
  eur_vars :: "variable_untyped list"
typedef expression_untyped = "{(e::expression_untyped_rep).
  (\<forall>m. eur_fun e m \<in> t_domain (eur_type e)) \<and>
  (\<forall>m1 m2. (\<forall>v\<in>set (eur_vars e). memory_lookup_untyped m1 v = memory_lookup_untyped m2 v) \<longrightarrow> eur_fun e m1 = eur_fun e m2)}"
  by (rule exI[of _ "\<lparr> eur_fun=(\<lambda>m. t_default undefined),
                          eur_type=undefined,
                          eur_vars=[] \<rparr>"], simp)
definition "eu_fun e == eur_fun (Rep_expression_untyped e)"
definition "eu_type e == eur_type (Rep_expression_untyped e)"
definition "eu_vars e == eur_vars (Rep_expression_untyped e)"


lemma eu_fun_type [simp]: "eu_fun e m \<in> t_domain (eu_type e)"
  using Rep_expression_untyped eu_fun_def eu_type_def by auto

lemma expression_type_inhabited: "\<exists>e. eu_type e = T"
  apply (rule exI[where x="Abs_expression_untyped \<lparr> eur_fun=(\<lambda>x. t_default T), eur_type=T, eur_vars=[] \<rparr>"])
  unfolding eu_type_def by (subst Abs_expression_untyped_inverse, auto)

record expression_distr_rep =
  edr_fun :: "memory \<Rightarrow> val distr"
  edr_type :: type
  edr_vars :: "variable_untyped list"
typedef expression_distr = "{(e::expression_distr_rep).
  (\<forall>m. support_distr (edr_fun e m) \<subseteq> t_domain (edr_type e)) \<and>
  (\<forall>m1 m2. (\<forall>v\<in>set (edr_vars e). memory_lookup_untyped m1 v = memory_lookup_untyped m2 v) \<longrightarrow> edr_fun e m1 = edr_fun e m2)}"
  by (rule exI[of _ "\<lparr> edr_fun=\<lambda>m. 0,
                          edr_type=undefined,
                          edr_vars=[] \<rparr>"], simp)

definition "ed_fun e == edr_fun (Rep_expression_distr e)"
definition "ed_type e == edr_type (Rep_expression_distr e)"
definition "ed_vars e == edr_vars (Rep_expression_distr e)"

definition const_expression_untyped :: "type \<Rightarrow> val \<Rightarrow> expression_untyped" where
  "const_expression_untyped T x = Abs_expression_untyped \<lparr> eur_fun=\<lambda>m. x, eur_type=T, eur_vars=[] \<rparr>"

lemma eu_fun_const_expression_untyped: "a \<in> t_domain T \<Longrightarrow> eu_fun (const_expression_untyped T a) = (\<lambda>m. a)"
  unfolding const_expression_untyped_def eu_fun_def
  by (subst Abs_expression_untyped_inverse, auto)
lemma eu_type_const_expression_untyped: "a \<in> t_domain T \<Longrightarrow> eu_type (const_expression_untyped T a) = T"
  unfolding const_expression_untyped_def eu_type_def
  by (subst Abs_expression_untyped_inverse, auto)
lemma eu_vars_const_expression_untyped: "a \<in> t_domain T \<Longrightarrow> eu_vars (const_expression_untyped T a) = []"
  unfolding const_expression_untyped_def eu_vars_def
  by (subst Abs_expression_untyped_inverse, auto)

lemma eu_fun_footprint: 
  assumes "\<And>v. v\<in>set (eu_vars e) \<Longrightarrow> memory_lookup_untyped m1 v = memory_lookup_untyped m2 v"
  shows "eu_fun e m1 = eu_fun e m2"
using Rep_expression_untyped assms eu_fun_def eu_vars_def by auto

lemma ed_fun_footprint: 
  assumes "\<And>v. v\<in>set (ed_vars e) \<Longrightarrow> memory_lookup_untyped m1 v = memory_lookup_untyped m2 v"
  shows "ed_fun e m1 = ed_fun e m2"
using Rep_expression_distr assms ed_fun_def ed_vars_def by auto

definition "expression_distr_zero T == Abs_expression_distr \<lparr> edr_fun=\<lambda>x. 0, edr_type=T, edr_vars=[] \<rparr>"

lemma ed_fun_const_expression_untyped [simp]: "ed_fun (expression_distr_zero T) = (\<lambda>m. 0)"
  unfolding expression_distr_zero_def ed_fun_def
  by (subst Abs_expression_distr_inverse, auto)
lemma ed_type_const_expression_untyped [simp]: "ed_type (expression_distr_zero T) = T"
  unfolding expression_distr_zero_def ed_type_def
  by (subst Abs_expression_distr_inverse, auto)
lemma ed_vars_const_expression_untyped [simp]: "ed_vars (expression_distr_zero T) = []"
  unfolding expression_distr_zero_def ed_vars_def
  by (subst Abs_expression_distr_inverse, auto)

definition var_expression_untyped :: "variable_untyped \<Rightarrow> expression_untyped" where
"var_expression_untyped v = Abs_expression_untyped
  \<lparr> eur_fun=\<lambda>m. memory_lookup_untyped m v,
    eur_type=vu_type v,
    eur_vars=[v] \<rparr>"
lemma Rep_var_expression_untyped: "Rep_expression_untyped (var_expression_untyped v) = 
  \<lparr> eur_fun=\<lambda>m. memory_lookup_untyped m v,
    eur_type=vu_type v,
    eur_vars=[v] \<rparr>"
  unfolding var_expression_untyped_def
  apply (subst Abs_expression_untyped_inverse)
  by auto
lemma eu_type_var_expression_untyped [simp]: "eu_type (var_expression_untyped x) = vu_type x"
  unfolding eu_type_def using Rep_var_expression_untyped by simp
lemma eu_fun_var_expression_untyped [simp]: "eu_fun (var_expression_untyped x) = (\<lambda>m. memory_lookup_untyped m x)"
  unfolding eu_fun_def using Rep_var_expression_untyped by simp
lemma eu_vars_var_expression_untyped [simp]: "eu_vars (var_expression_untyped x) = [x]"
  unfolding eu_vars_def using Rep_var_expression_untyped by simp


definition pair_expression_untyped :: "expression_untyped \<Rightarrow> expression_untyped \<Rightarrow> expression_untyped" where
  "pair_expression_untyped e1 e2 = Abs_expression_untyped
   \<lparr> eur_fun = (\<lambda>m. val_prod_embedding (eu_fun e1 m, eu_fun e2 m)),
     eur_type = prod_type (eu_type e1) (eu_type e2),
     eur_vars = eu_vars e1 @ eu_vars e2 \<rparr>"
lemma Rep_pair_expression_untyped: "Rep_expression_untyped (pair_expression_untyped e1 e2) =
   \<lparr> eur_fun = (\<lambda>m. val_prod_embedding (eu_fun e1 m, eu_fun e2 m)),
     eur_type = prod_type (eu_type e1) (eu_type e2),
     eur_vars = eu_vars e1 @ eu_vars e2 \<rparr>"
  unfolding pair_expression_untyped_def
  apply (subst Abs_expression_untyped_inverse)
  apply auto by (metis UnCI eu_fun_footprint)
lemma eu_fun_pair_expression_untyped: "eu_fun (pair_expression_untyped e1 e2) = (\<lambda>m. val_prod_embedding (eu_fun e1 m, eu_fun e2 m))"
  using Rep_pair_expression_untyped unfolding eu_fun_def by auto
lemma eu_type_pair_expression_untyped [simp]: "eu_type (pair_expression_untyped e1 e2) = prod_type (eu_type e1) (eu_type e2)"
  using Rep_pair_expression_untyped unfolding eu_type_def by auto
lemma eu_vars_pair_expression_untyped [simp]: "eu_vars (pair_expression_untyped e1 e2) = eu_vars e1 @ eu_vars e2"
  using Rep_pair_expression_untyped unfolding eu_vars_def by auto


fun list_expression_untyped :: "variable_untyped list \<Rightarrow> expression_untyped" where
  "list_expression_untyped [] = const_expression_untyped unit_type (embedding (default::unit))"
| "list_expression_untyped (x#xs) = pair_expression_untyped (var_expression_untyped x) (list_expression_untyped xs)"

lemma eu_vars_list_expression_untyped [simp]: "eu_vars (list_expression_untyped xs) = xs"
  apply (induction xs) by (auto intro!: eu_vars_const_expression_untyped)

subsection {* Patterns *}

record pattern_rep =
  pur_var_getters :: "(variable_untyped*(val\<Rightarrow>val)) list"
  pur_type :: "type"

typedef pattern_untyped = "{(p::pattern_rep). 
  (\<forall>(v,f)\<in>set(pur_var_getters p). 
    ((\<forall>x. f x \<in> t_domain (vu_type v)) \<and> (\<forall>x\<in>-t_domain (pur_type p). f x = t_default (vu_type v))))}"
  by (rule exI[of _ "\<lparr> pur_var_getters=[], pur_type=undefined \<rparr>"], simp)


definition "pu_var_getters p = pur_var_getters (Rep_pattern_untyped p)"
definition "pu_vars p = map fst (pu_var_getters p)"
definition "pu_type p = pur_type (Rep_pattern_untyped p)"

definition "pattern_1var v = Abs_pattern_untyped \<lparr> pur_var_getters=[(v, \<lambda>x. if x\<in>t_domain(vu_type v) then x else t_default(vu_type v))], pur_type=vu_type v \<rparr>"
lemma Rep_pattern_1var: "Rep_pattern_untyped (pattern_1var v) = \<lparr> pur_var_getters=[(v, \<lambda>x. if x\<in>t_domain(vu_type v) then x else t_default(vu_type v))], pur_type=vu_type v \<rparr>"
  unfolding  pu_var_getters_def pattern_1var_def 
  apply (subst Abs_pattern_untyped_inverse) by auto
lemma p_var_getters_pattern_1var [simp]: "pu_var_getters (pattern_1var v) = [(v, \<lambda>x. if x\<in>t_domain(vu_type v) then x else t_default(vu_type v))]"
  unfolding  pu_var_getters_def pattern_1var_def 
  apply (subst Abs_pattern_untyped_inverse) by auto
lemma p_vars_pattern_1var [simp]: "pu_vars (pattern_1var v) = [v]"
  unfolding pu_vars_def by simp
lemma p_type_pattern_1var [simp]: "pu_type (pattern_1var v) = vu_type v"
  by (simp add: Abs_pattern_untyped_inverse pu_type_def pattern_1var_def)

definition "pattern_ignore T = Abs_pattern_untyped \<lparr> pur_var_getters=[], pur_type=T \<rparr>"
lemma Rep_pattern_ignore: "Rep_pattern_untyped (pattern_ignore T) = \<lparr> pur_var_getters=[], pur_type=T \<rparr>"
  by (simp add: Abs_pattern_untyped_inverse pattern_ignore_def)
lemma p_var_getters_pattern_ignore [simp]: "pu_var_getters (pattern_ignore T) = []"
  by (simp add: Abs_pattern_untyped_inverse pu_var_getters_def pattern_ignore_def)
lemma p_vars_pattern_ignore [simp]: "pu_vars (pattern_ignore T) = []"
  unfolding pu_vars_def by simp
lemma p_type_pattern_ignore [simp]: "pu_type (pattern_ignore T) = T"
  by (simp add: Abs_pattern_untyped_inverse pu_type_def pattern_ignore_def)


lemma no_vars_ignore_pattern_untyped: "pu_vars p = [] \<Longrightarrow> p = pattern_ignore (pu_type p)"
proof -
  assume "pu_vars p = []"
  hence "pu_var_getters p = []"
    unfolding pu_vars_def pu_var_getters_def by auto
  moreover have "pu_type p = pu_type (pattern_ignore (pu_type p))"
    by simp
  ultimately show ?thesis
    by (metis (full_types) Rep_pattern_untyped_inverse old.unit.exhaust pattern_ignore_def pattern_rep.surjective pu_type_def pu_var_getters_def) 
qed

definition pair_pattern_untyped :: "pattern_untyped \<Rightarrow> pattern_untyped \<Rightarrow> pattern_untyped" where
  "pair_pattern_untyped p1 p2 = (let T = prod_type (pu_type p1) (pu_type p2) in Abs_pattern_untyped 
  \<lparr> pur_var_getters=(map (\<lambda>(v,g). (v,\<lambda>x. if x\<in>t_domain T then (g o fst o inv val_prod_embedding) x else t_default (vu_type v))) (pu_var_getters p1))
                  @ (map (\<lambda>(v,g). (v,\<lambda>x. if x\<in>t_domain T then (g o snd o inv val_prod_embedding) x else t_default (vu_type v))) (pu_var_getters p2)),
    pur_type=T \<rparr>)"

lemma Rep_pair_pattern_untyped: "Rep_pattern_untyped (pair_pattern_untyped p1 p2) = (let T = prod_type (pu_type p1) (pu_type p2) in
  \<lparr> pur_var_getters=(map (\<lambda>(v,g). (v,\<lambda>x. if x\<in>t_domain T then (g o fst o inv val_prod_embedding) x else t_default (vu_type v))) (pu_var_getters p1))
                  @ (map (\<lambda>(v,g). (v,\<lambda>x. if x\<in>t_domain T then (g o snd o inv val_prod_embedding) x else t_default (vu_type v))) (pu_var_getters p2)),
    pur_type=T \<rparr>)"
unfolding pair_pattern_untyped_def Let_def
apply (subst Abs_pattern_untyped_inverse)
apply auto
using Rep_pattern_untyped pu_var_getters_def by fastforce+

lemma pu_type_pair_pattern [simp]: "pu_type (pair_pattern_untyped p1 p2) = prod_type (pu_type p1) (pu_type p2)"
  unfolding pu_type_def Rep_pair_pattern_untyped by simp

lemma pu_var_getters_pair_pattern [simp]: "pu_var_getters (pair_pattern_untyped p1 p2) = 
    (let T = pu_type (pair_pattern_untyped p1 p2) in
                    (map (\<lambda>(v,g). (v,\<lambda>x. if x\<in>t_domain T then (g o fst o inv val_prod_embedding) x else t_default (vu_type v))) (pu_var_getters p1))
                  @ (map (\<lambda>(v,g). (v,\<lambda>x. if x\<in>t_domain T then (g o snd o inv val_prod_embedding) x else t_default (vu_type v))) (pu_var_getters p2)))"
  unfolding pu_var_getters_def Rep_pair_pattern_untyped by simp                                          

lemma pu_vars_pair_pattern [simp]: "pu_vars (pair_pattern_untyped p1 p2) = pu_vars p1 @ pu_vars p2"
  unfolding pu_vars_def by (simp add: case_prod_unfold)




definition memory_update_untyped_pattern :: "memory \<Rightarrow> pattern_untyped \<Rightarrow> val \<Rightarrow> memory" where
  "memory_update_untyped_pattern m p x = 
  foldl (\<lambda>m (v,f). memory_update_untyped m v (f x)) m (pu_var_getters p)"

definition memory_update_untyped_pattern_getter :: "pattern_untyped \<Rightarrow> variable_untyped \<Rightarrow> val \<Rightarrow> val" where
  "memory_update_untyped_pattern_getter pat v =
  (case List.find (\<lambda>(w,f). v=w) (rev (pu_var_getters pat)) of Some (w,f) \<Rightarrow> f | None \<Rightarrow> undefined)"

lemma lookup_memory_update_untyped_pattern_getter:
  assumes "v \<in> set (pu_vars pat)"
  shows "memory_lookup_untyped (memory_update_untyped_pattern m pat val) v = memory_update_untyped_pattern_getter pat v val"
proof -
  define getters where "getters \<equiv> pu_var_getters pat"
  have vgetters: "v \<in> fst ` set getters"
    using assms getters_def pu_vars_def by auto
  define good where "good \<equiv> \<lambda>(v::variable_untyped,f::val\<Rightarrow>val). (\<forall>x. f x \<in> t_domain (vu_type v))"
  have good: "\<forall>getter \<in> set getters. good getter"
    using Rep_pattern_untyped unfolding getters_def good_def pu_var_getters_def apply auto by blast
  show ?thesis
    unfolding memory_update_untyped_pattern_def memory_update_untyped_pattern_getter_def getters_def[symmetric]
  proof (insert vgetters, insert good, induct getters arbitrary: m v rule:rev_induct)
  case Nil thus ?case by auto
  next case (snoc getter getters)
    obtain z f where zf: "getter = (z,f)" by fastforce
    have good: "\<forall>a\<in>set (getters @ [getter]). good a" using snoc by simp
    show ?case
    proof (cases "v=z")
    case True
      show ?thesis
        apply (simp add: zf True)
        apply (rule memory_lookup_update_same_untyped)
        using good zf good_def True by auto
    next case False
      show ?thesis
        apply (simp add: zf False)
        apply (subst memory_lookup_update_notsame_untyped)
         using False close simp
        apply (subst snoc.hyps)
        using snoc.prems zf False by auto
    qed
  qed
qed

lemma memory_update_untyped_pattern_footprint: (* TODO replace by stronger one below *)
  assumes "\<And>v. v\<in>X \<Longrightarrow> memory_lookup_untyped m1 v = memory_lookup_untyped m2 v"
  assumes "X \<supseteq> set (pu_vars pat)"
  shows   "\<And>v. v\<in>X \<Longrightarrow> memory_lookup_untyped (memory_update_untyped_pattern m1 pat x) v = memory_lookup_untyped (memory_update_untyped_pattern m2 pat x) v"
proof -
  fix v
  define getters where "getters == pu_var_getters pat"
  have "\<And>gv gs. (gv,gs)\<in>set getters \<Longrightarrow> gv \<in> set (pu_vars pat)" 
    unfolding getters_def pu_vars_def by force
  hence gvX: "\<And>gv gs. (gv,gs)\<in>set getters \<Longrightarrow> gv \<in> X"
    using assms(2) by auto
  show "v\<in>X \<Longrightarrow> memory_lookup_untyped (memory_update_untyped_pattern m1 pat x) v = memory_lookup_untyped (memory_update_untyped_pattern m2 pat x) v"
    unfolding memory_update_untyped_pattern_def getters_def[symmetric]
  proof (insert gvX, induct getters arbitrary: v rule:rev_induct)
  case Nil thus ?case using assms(1) by simp
  next case (snoc g gs)
    obtain gv gf where g:"g = (gv,gf)" by force
    have gvX: "gv \<in> X" using snoc.prems g by auto
    have gs: "\<And>gv gf. (gv, gf) \<in> set gs \<Longrightarrow> gv \<in> X"
      using snoc.prems(2) by force
    have eq: "\<And>v. v \<in> X \<Longrightarrow>
         memory_lookup_untyped (foldl (\<lambda>m (v, f). memory_update_untyped m v (f x)) m1 gs) v =
         memory_lookup_untyped (foldl (\<lambda>m (v, f). memory_update_untyped m v (f x)) m2 gs) v"
     using snoc.hyps gs by auto
    show ?case 
      unfolding g apply simp
      apply (rule memory_update_untyped_footprint[where X=X])
      using snoc gvX eq by simp_all
  qed
qed

lemma memory_update_untyped_pattern_footprint_STRONGER:
  assumes "\<And>v. v\<in>X \<Longrightarrow> memory_lookup_untyped m1 v = memory_lookup_untyped m2 v"
  shows   "\<And>v. v\<in>X \<Longrightarrow> memory_lookup_untyped (memory_update_untyped_pattern m1 pat x) v = memory_lookup_untyped (memory_update_untyped_pattern m2 pat x) v"
proof -
  fix v
  define getters where "getters == pu_var_getters pat"
  have "\<And>gv gs. (gv,gs)\<in>set getters \<Longrightarrow> gv \<in> set (pu_vars pat)" 
    unfolding getters_def pu_vars_def by force
  show "v\<in>X \<Longrightarrow> memory_lookup_untyped (memory_update_untyped_pattern m1 pat x) v = memory_lookup_untyped (memory_update_untyped_pattern m2 pat x) v"
    unfolding memory_update_untyped_pattern_def getters_def[symmetric]
  proof (induct getters arbitrary: v rule:rev_induct)
  case Nil thus ?case using assms(1) by simp
  next case (snoc g gs)
    obtain gv gf where g:"g = (gv,gf)" by force
    have eq: "\<And>v. v \<in> X \<Longrightarrow>
         memory_lookup_untyped (foldl (\<lambda>m (v, f). memory_update_untyped m v (f x)) m1 gs) v =
         memory_lookup_untyped (foldl (\<lambda>m (v, f). memory_update_untyped m v (f x)) m2 gs) v"
     using snoc.hyps by auto
    show ?case 
      unfolding g apply simp
      apply (rule memory_update_untyped_footprint_STRONGER[where X=X])
      using snoc eq by simp_all
  qed
qed


lemma memory_lookup_update_pattern_notsame:
  assumes "x \<notin> set (pu_vars p)"
  shows "memory_lookup_untyped (memory_update_untyped_pattern m p a) x = memory_lookup_untyped m x"
proof -
  define vg where "vg == pu_var_getters p"
  hence vg: "x \<notin> fst ` set vg"
    using assms pu_var_getters_def pu_vars_def by auto
  show ?thesis
    unfolding memory_update_untyped_pattern_def  vg_def[symmetric]
    apply (insert vg)
    apply (induct vg rule:rev_induct)
     by (auto simp: memory_lookup_update_notsame_untyped)
qed


lemma memory_update_untyped_pattern_1var [simp]: 
  assumes "z \<in> t_domain (vu_type x)"
  shows "memory_update_untyped_pattern m (pattern_1var x) z = memory_update_untyped m x z"
by (simp add: assms memory_update_untyped_pattern_def)

lemma memory_update_untyped_pattern_ignore [simp]:
  "memory_update_untyped_pattern m (pattern_ignore x) = (\<lambda>_. m)"
by (rule ext, simp add: memory_update_untyped_pattern_def)

lemma memory_update_pair_pattern_untyped:
  assumes "x1 \<in> t_domain (pu_type p1)" and "x2 \<in> t_domain (pu_type p2)"
  shows "memory_update_untyped_pattern m (pair_pattern_untyped p1 p2) (val_prod_embedding (x1,x2)) = memory_update_untyped_pattern (memory_update_untyped_pattern m p1 x1) p2 x2"
proof -
  define p1vg p2vg T fstg sndg 
     where "p1vg == pu_var_getters p1"
       and "p2vg == pu_var_getters p2"
       and "T == pu_type (pair_pattern_untyped p1 p2)"
       and "fstg == \<lambda>(v::variable_untyped) g. \<lambda>x. if x \<in> t_domain T then (g \<circ> fst \<circ> inv val_prod_embedding) x else t_default (vu_type v)"
       and "sndg == \<lambda>(v::variable_untyped) g. \<lambda>x. if x \<in> t_domain T then (g \<circ> snd \<circ> inv val_prod_embedding) x else t_default (vu_type v)"

  from assms have x1x2_T: "val_prod_embedding (x1,x2) \<in> t_domain T"
    unfolding T_def pu_type_pair_pattern t_domain_prod by simp

  have fst_simp: "memory_update_untyped m (fst vf) (fstg (fst vf) (snd vf) (val_prod_embedding (x1, x2)))
     = memory_update_untyped m (fst vf) (snd vf x1)" for vf m 
     unfolding fstg_def apply (simp add: x1x2_T) apply (subst inv_f_f[OF inj_val_prod_embedding]) by simp
  have snd_simp: "memory_update_untyped m (fst vf) (sndg (fst vf) (snd vf) (val_prod_embedding (x1, x2)))
     = memory_update_untyped m (fst vf) (snd vf x2)" for vf m 
     unfolding sndg_def apply (simp add: x1x2_T) apply (subst inv_f_f[OF inj_val_prod_embedding]) by simp

  have "foldl (\<lambda>m (v, f). memory_update_untyped m v (f (val_prod_embedding (x1, x2)))) m
     (map (\<lambda>(v, g). (v, fstg v g)) p1vg @
      map (\<lambda>(v, g). (v, sndg v g)) p2vg) =
    foldl (\<lambda>m (v, f). memory_update_untyped m v (f x2)) (foldl (\<lambda>m (v, f). memory_update_untyped m v (f x1)) m p1vg) p2vg"
      unfolding foldl_append split_def foldl_map apply simp
      unfolding fst_simp snd_simp by simp

  thus ?thesis
    unfolding memory_update_untyped_pattern_def pu_var_getters_pair_pattern p1vg_def[symmetric] 
        p2vg_def[symmetric] T_def[symmetric] fstg_def sndg_def Let_def by simp
qed


fun list_pattern_untyped :: "variable_untyped list \<Rightarrow> pattern_untyped" where
  "list_pattern_untyped [] = pattern_ignore unit_type"
| "list_pattern_untyped (x#xs) = pair_pattern_untyped (pattern_1var x) (list_pattern_untyped xs)"


lemma pu_vars_list_pattern_untyped [simp]: "pu_vars (list_pattern_untyped xs) = xs"
  apply (induction xs) by auto


lemma list_pattern_untyped_list_expression_untyped: "memory_update_untyped_pattern m (list_pattern_untyped xs) (eu_fun (list_expression_untyped xs) m) = m"
proof (induction xs arbitrary: m)
case Nil show ?case by auto
next case (Cons x xs')
  have type: "pu_type (list_pattern_untyped xs) = eu_type (list_expression_untyped xs)" for xs
  proof (induction xs)
  case Nil show ?case apply simp apply (subst eu_type_const_expression_untyped) by auto
  next case Cons thus ?case by auto
  qed
  have u1: "memory_update_untyped_pattern m (pattern_1var x) (eu_fun (var_expression_untyped x) m) = m"
    by simp
  have u2: "memory_update_untyped_pattern (memory_update_untyped_pattern m (pattern_1var x) (eu_fun (var_expression_untyped x) m))
     (list_pattern_untyped xs') (eu_fun (list_expression_untyped xs') m) = m"
    apply (subst u1) by (fact Cons)

  show ?case
    apply (simp add: eu_fun_pair_expression_untyped)
    apply (subst memory_update_pair_pattern_untyped)
      close (auto simp: Rep_var_expression_untyped eu_fun_def)
     using type close simp
    using u2 by simp
qed


lemma list_expression_list_pattern_untyped:
  assumes "distinct x"
  assumes "v \<in> t_domain (pu_type (list_pattern_untyped x))"
  shows "eu_fun (list_expression_untyped x) (memory_update_untyped_pattern m (list_pattern_untyped x) v) = v"
using assms proof (induction x arbitrary: m v)
case Nil thus ?case by (simp add: eu_fun_const_expression_untyped)
next case (Cons x xs)
  obtain u w where v: "v = val_prod_embedding (u,w)" apply atomize_elim using Cons.prems by auto
  have u: "u \<in> t_domain (pu_type (pattern_1var x))"
    by (smt Cons.prems(2) imageE inj_val_prod_embedding inv_f_f list_pattern_untyped.simps(2) mem_Sigma_iff pu_type_pair_pattern t_domain_prod v)
  have w: "w \<in> t_domain (pu_type (list_pattern_untyped xs))"
    by  (smt Cons.prems(2) imageE inj_val_prod_embedding inv_f_f list_pattern_untyped.simps(2) mem_Sigma_iff pu_type_pair_pattern t_domain_prod v)

  have t1: "memory_lookup_untyped (memory_update_untyped_pattern (memory_update_untyped_pattern m
            (pattern_1var x) u) (list_pattern_untyped xs) w) x = u"
    apply (subst memory_lookup_update_pattern_notsame)
     using Cons.prems memory_lookup_update_same_untyped u by auto

  show "eu_fun (list_expression_untyped (x # xs)) (memory_update_untyped_pattern m (list_pattern_untyped (x # xs)) v)
      = v"
    apply (simp add: eu_fun_pair_expression_untyped v)
    apply (subst memory_update_pair_pattern_untyped[OF u w])
    apply (subst memory_update_pair_pattern_untyped[OF u w])
    apply (subst Cons.IH)
      using Cons w close 2
    apply (subst t1)
    by rule
qed  


lemma type_list_expression_list_pattern: "eu_type (list_expression_untyped xs) = pu_type (list_pattern_untyped xs)"
  apply (induction xs)
   close (simp add: eu_type_const_expression_untyped)
  by auto


definition "kill_vars_pattern_untyped p X = Abs_pattern_untyped
  \<lparr> pur_var_getters = filter (\<lambda>(v,g). v \<notin> X) (pu_var_getters p),
    pur_type = pu_type p \<rparr>"
lemma Rep_kill_vars_pattern_untyped: "Rep_pattern_untyped (kill_vars_pattern_untyped p X) =
  \<lparr> pur_var_getters = filter (\<lambda>(v,g). v \<notin> X) (pu_var_getters p),
    pur_type = pu_type p \<rparr>"
      unfolding kill_vars_pattern_untyped_def apply (rule Abs_pattern_untyped_inverse)
      apply auto
      using Rep_pattern_untyped pu_var_getters_def close force
      using Rep_pattern_untyped unfolding pu_var_getters_def split_def
      using pu_type_def by fastforce 
lemma pu_type_kill_vars_pattern_untyped [simp]: "pu_type (kill_vars_pattern_untyped p X) = pu_type p"
  unfolding pu_type_def Rep_kill_vars_pattern_untyped by simp
lemma pu_var_getters_kill_vars_pattern_untyped: "pu_var_getters (kill_vars_pattern_untyped p X) = filter (\<lambda>(v,g). v \<notin> X) (pu_var_getters p)"
  unfolding pu_var_getters_def Rep_kill_vars_pattern_untyped by simp
lemma pu_vars_kill_vars_pattern_untyped: "pu_vars (kill_vars_pattern_untyped p X) = filter (\<lambda>v. v \<notin> X) (pu_vars p)"
  unfolding pu_vars_def pu_var_getters_kill_vars_pattern_untyped split_def filter_map o_def by simp


lemma kill_vars_pattern_untyped_twice:
   "kill_vars_pattern_untyped (kill_vars_pattern_untyped p X) Y = kill_vars_pattern_untyped p (X\<union>Y)"
apply (subst Rep_pattern_untyped_inject[symmetric])
unfolding Rep_kill_vars_pattern_untyped pu_var_getters_def split_def
by auto

lemma kill_vars_pattern_untyped_disjoint:
  assumes "set (pu_vars p) \<inter> X = {}"
  shows "kill_vars_pattern_untyped p X = p"
proof -
  define vgp where "vgp == pu_var_getters p"
  have vgX: "fst vg \<notin> X" if "vg \<in> set vgp" for vg
    using assms pu_vars_def that vgp_def by auto 
  have getters: "[(v, g)\<leftarrow>pu_var_getters p . v \<notin> X] = pu_var_getters p"
    unfolding vgp_def[symmetric]
    apply (insert vgX, induction vgp) apply auto by blast
  show ?thesis
    apply (subst Rep_pattern_untyped_inject[symmetric])
    unfolding Rep_kill_vars_pattern_untyped
    using getters by (simp add: old.unit.exhaust pattern_rep.surjective pu_type_def pu_var_getters_def) 
qed

lemma kill_vars_pattern_untyped_empty [simp]: "kill_vars_pattern_untyped p {} = p"
  by (rule kill_vars_pattern_untyped_disjoint, simp)

lemma memory_update_pattern_getter_kill_vars_pattern_untyped:
  assumes "x \<notin> X"
  shows "memory_update_untyped_pattern_getter (kill_vars_pattern_untyped p X) x = memory_update_untyped_pattern_getter p x"
proof -
  define rg where "rg == rev (pu_var_getters p)"
  have t: "find (\<lambda>p. x = fst p) [p\<leftarrow>rg . fst p \<notin> X] = find (\<lambda>p. x = fst p) rg"
    apply (induction rg) close
    using `x\<notin>X` by auto
  show ?thesis
    unfolding memory_update_untyped_pattern_getter_def pu_var_getters_kill_vars_pattern_untyped 
          split_def rev_filter rg_def[symmetric]
    using t by simp
qed

lemma memory_update_pattern_twice_kill_untyped: 
  "memory_update_untyped_pattern (memory_update_untyped_pattern m p x) q y = 
   memory_update_untyped_pattern (memory_update_untyped_pattern m (kill_vars_pattern_untyped p (set (pu_vars q))) x) q y"
proof (rule memory_lookup_untyped_inject[OF ext], case_tac "v \<in> set (pu_vars q)")
  fix v
  assume v: "v \<in> set (pu_vars q)"
  show "memory_lookup_untyped (memory_update_untyped_pattern (memory_update_untyped_pattern m p x) q y) v =
         memory_lookup_untyped
          (memory_update_untyped_pattern (memory_update_untyped_pattern m (kill_vars_pattern_untyped p (set (pu_vars q))) x) q y) v"
    apply (subst lookup_memory_update_untyped_pattern_getter) using v close
    apply (subst lookup_memory_update_untyped_pattern_getter) using v close
    by simp    
next
  fix v
  assume vq: "v \<notin> set (pu_vars q)"
  have eqp: "memory_lookup_untyped (memory_update_untyped_pattern m p x) v =
             memory_lookup_untyped (memory_update_untyped_pattern m (kill_vars_pattern_untyped p (set (pu_vars q))) x) v"
  proof (cases "v\<in>set(pu_vars p)")
  case True
    hence vkill: "v \<in> set (pu_vars (kill_vars_pattern_untyped p (set (pu_vars q))))"
      unfolding pu_vars_kill_vars_pattern_untyped using vq by simp
    show ?thesis 
      apply (subst lookup_memory_update_untyped_pattern_getter) using True close
      apply (subst lookup_memory_update_untyped_pattern_getter) using vkill close
      apply (subst memory_update_pattern_getter_kill_vars_pattern_untyped) using vq close
      by simp
  next case False
    hence vkill: "v \<notin> set (pu_vars (kill_vars_pattern_untyped p (set (pu_vars q))))"
      unfolding pu_vars_kill_vars_pattern_untyped by simp
    show ?thesis 
      apply (subst memory_lookup_update_pattern_notsame) using False close
      apply (subst memory_lookup_update_pattern_notsame) using vkill close
      by simp
  qed
  show "memory_lookup_untyped (memory_update_untyped_pattern (memory_update_untyped_pattern m p x) q y) v =
         memory_lookup_untyped
          (memory_update_untyped_pattern (memory_update_untyped_pattern m (kill_vars_pattern_untyped p (set (pu_vars q))) x) q y) v"
    apply (subst memory_lookup_update_pattern_notsame[where p=q]) using vq close
    apply (subst memory_lookup_update_pattern_notsame[where p=q]) using vq close
    using eqp by simp
qed

lemma memory_update_update_pattern_untyped_swap: 
  "memory_update_untyped (memory_update_untyped_pattern m a aval) x xval
  = memory_update_untyped_pattern (memory_update_untyped m x xval) (kill_vars_pattern_untyped a {x}) aval"
proof -
  define vgs where "vgs == pu_var_getters a"
  define mup where "mup == \<lambda>m (v,f). memory_update_untyped m v (f aval)"
  have killed: "pu_var_getters (kill_vars_pattern_untyped a {x}) = [(v, g)\<leftarrow>pu_var_getters a . v \<noteq> x]"
    unfolding pu_var_getters_kill_vars_pattern_untyped by simp
  have mup_swap: "memory_update_untyped (mup m xf) y val = mup (memory_update_untyped m y val) xf" if "y \<noteq> fst xf" for xf y val m
    unfolding mup_def using that apply (cases xf) by (simp add: memory_update_untyped_twice_notsame)
  have mup_swap': "memory_update_untyped (mup m xf) y val = memory_update_untyped m y val" if "y = fst xf" for xf y val m
    unfolding mup_def apply (cases xf) using that by simp
  show ?thesis
    unfolding memory_update_untyped_pattern_def vgs_def[symmetric] killed mup_def[symmetric]
    proof (induction vgs rule:rev_induct)
    case Nil show ?case by simp
    next case (snoc vg vgs)
      show ?case 
      proof (cases "x = fst vg")
      case False thus ?thesis apply auto apply (subst snoc[symmetric]) apply (subst mup_swap) by auto
      next case True thus ?thesis apply auto apply (subst (asm) snoc[symmetric]) apply (subst (asm) mup_swap') by auto
    qed
  qed
qed

lemma memory_update_pattern_untyped_swap: "memory_update_untyped_pattern (memory_update_untyped_pattern m a x) b y
     = memory_update_untyped_pattern (memory_update_untyped_pattern m b y) (kill_vars_pattern_untyped a (set (pu_vars b))) x"
proof -
  define vgb where "vgb == pu_var_getters b"
  hence upb: "memory_update_untyped_pattern m b x = foldl (\<lambda>m (v, f). memory_update_untyped m v (f x)) m vgb" for x m
    unfolding memory_update_untyped_pattern_def by simp
  have vb: "pu_vars b = map fst vgb" by (simp add: vgb_def pu_vars_def)
    
  define mup where "mup == \<lambda>m (v,f). memory_update_untyped m v (f y)"

  have commute:
       "mup (memory_update_untyped_pattern m (kill_vars_pattern_untyped a X) aval) xf 
      = memory_update_untyped_pattern (mup m xf) (kill_vars_pattern_untyped a (X\<union>{fst xf})) aval" for m X xf aval
    unfolding mup_def apply (cases xf)
    apply auto
    apply (subst memory_update_update_pattern_untyped_swap)
    apply (subst kill_vars_pattern_untyped_twice)
    by auto
    
  show ?thesis
    unfolding upb vb mup_def[symmetric]
  proof (induction vgb rule:rev_induct)
  case Nil show ?case by simp
  next case (snoc vg vgb)
    show ?case
      apply auto
      apply (subst snoc)
      apply (subst commute)
      by auto
  qed
qed

subsection {* Procedures *}

record procedure_type =
  pt_argtype :: "type"
  pt_returntype :: "type"

datatype program_rep =
  Assign pattern_untyped expression_untyped
     (* Assign vars getters exp \<rightarrow> the getters are applied to the result of exp and assigned to the variables *)
| Sample pattern_untyped expression_distr
| Seq program_rep program_rep
| Skip
| IfTE expression_untyped program_rep program_rep
| While expression_untyped program_rep
| CallProc pattern_untyped procedure_rep expression_untyped
and procedure_rep =
  Proc program_rep pattern_untyped expression_untyped
| ProcRef nat (* deBruijn index *)
| ProcUnit
| ProcAbs procedure_rep
| ProcAppl procedure_rep procedure_rep
| ProcPair procedure_rep procedure_rep
| ProcUnpair bool procedure_rep (* ProcUnpair True = fst, ProcUnpair False = snd *)

(*
fun is_concrete_proc where 
  "is_concrete_proc (Proc x y z) = True"
| "is_concrete_proc (ProcRef x T) = False"
*)

fun proctype_of :: "procedure_rep \<Rightarrow> procedure_type" where
  "proctype_of (Proc body argpat return) = \<lparr> pt_argtype=pu_type argpat, pt_returntype=eu_type return \<rparr>"
| "proctype_of _ = undefined" (* Cannot happen for well-typed programs *)

subsection {* Well-typed programs *}

fun well_typed :: "program_rep \<Rightarrow> bool" where
  "well_typed (Seq p1 p2) = (well_typed p1 \<and> well_typed p2)"
| "well_typed (Assign pat e) = (pu_type pat = eu_type e)"
| "well_typed (Sample pat e) = (pu_type pat = ed_type e)"
| "well_typed Skip = True"
| "well_typed (While e p) = ((eu_type e = bool_type) \<and> well_typed p)"
| "well_typed (IfTE e thn els) = ((eu_type e = bool_type) \<and> well_typed thn \<and> well_typed els)"
| "well_typed (CallProc v (Proc body argpat ret) args) =
    (pu_type v = eu_type ret \<and> 
    eu_type args = pu_type argpat \<and>
    well_typed body)" (* \<and> (\<forall>v\<in>set(p_vars argpat). \<not> vu_global v) *)
| "well_typed (CallProc v _ args) = False"

fun well_typed_proc :: "procedure_rep \<Rightarrow> bool" where
  "well_typed_proc (Proc body argpat ret) = 
    (well_typed body)" (*  \<and> (\<forall>v\<in>set(pu_vars argpat). \<not> vu_global v) *)
| "well_typed_proc _ = False"

typedef program = "{prog. well_typed prog}"
  apply (rule exI[where x=Skip]) by simp
(* abbreviation "mk_program_untyped == Rep_program" *)

lemma well_typed_Rep_program [simp]: "well_typed (Rep_program x)" 
  using Rep_program by simp

definition "Halt = Sample (pattern_ignore unit_type) (expression_distr_zero unit_type)"

fun While_n :: "nat \<Rightarrow> expression_untyped \<Rightarrow> program_rep \<Rightarrow> program_rep" where
  "While_n 0 e p = Halt"
| "While_n (Suc n) e p = IfTE e (Seq p (While_n n e p)) Skip"

(* While_n n + While_n_exact n = While_n (n+1) *)
fun While_n_exact :: "nat \<Rightarrow> expression_untyped \<Rightarrow> program_rep \<Rightarrow> program_rep" where
  "While_n_exact 0 e p =                                           IfTE e Halt Skip"
(* | "While_n_exact (Suc 0) e p =                      IfTE e (Seq p (IfTE e (Seq p Halt) Skip)) Halt" *)
(* | "While_n_exact (Suc (Suc 0)) e p = IfTE e (Seq p (IfTE e (Seq p (IfTE e (Seq p Halt) Skip)) Halt)) Halt" *)
(* TODO etc *)
| "While_n_exact (Suc n) e p = IfTE e (Seq p (While_n_exact n e p)) Halt"

subsection {* Denotational semantics *}

type_synonym denotation = "memory \<Rightarrow> memory distr"

(* TODO remove *)
(* fun while_iter :: "nat \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> denotation \<Rightarrow> memory \<Rightarrow> memory distr" where
  "while_iter 0 e p m = point_distr m"
| "while_iter (Suc n) e p m = 
      compose_distr (\<lambda>m. if e m then p m else 0)
                    (while_iter n e p m)" *)

(* while_denotation_n 3 e p m   is approximately:
   if e then (p; if e then (p; if e then p else skip))) *)
fun while_denotation_n :: "nat \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> denotation \<Rightarrow> denotation" where
  "while_denotation_n 0 e p m = 0"
| "while_denotation_n (Suc n) e p m =
    (if e m then compose_distr (while_denotation_n n e p) (p m) else point_distr m)"

lemma mono_while_denotation_n: "mono (\<lambda>n. while_denotation_n n e p m)"
proof -
  {fix n
  have "while_denotation_n n e p m \<le> while_denotation_n (Suc n) e p m"
  proof (induct n arbitrary: m)
  case 0
    show ?case by (simp add: bot_distr_def[symmetric])
  next case (Suc n)
    show ?case
    proof (cases "e m")
    case False
      thus ?thesis by simp
    next case True
      have "compose_distr (while_denotation_n n e p) (p m) \<le> compose_distr (while_denotation_n (Suc n) e p) (p m)" 
        using mono_compose_distr1 Suc unfolding mono_def le_fun_def[THEN ext] by blast
      with True show ?thesis by auto
    qed
  qed}
  thus ?thesis
    by (simp add: incseq_SucI)
qed



definition "init_locals m = Abs_memory (\<lambda>x. if vu_global x then Rep_memory m x else t_default (vu_type x))"
lemma Rep_init_locals: "Rep_memory (init_locals m) = (\<lambda>x. if vu_global x then Rep_memory m x else t_default (vu_type x))"
  unfolding init_locals_def apply (subst Abs_memory_inverse) using Rep_memory by auto
definition "restore_locals oldmem newmem = Abs_memory (\<lambda>x. if vu_global x then Rep_memory newmem x else Rep_memory oldmem x)"
lemma Rep_restore_locals: "Rep_memory (restore_locals oldmem newmem) = (\<lambda>x. if vu_global x then Rep_memory newmem x else Rep_memory oldmem x)"
  unfolding restore_locals_def apply (subst Abs_memory_inverse) using Rep_memory by auto

(*
definition "init_locals pargs args m = 
  (let args = map (\<lambda>e. eu_fun e m) args;
       m = Abs_memory (Rep_memory m\<lparr> mem_locals := (\<lambda>v. t_default (vu_type v)) \<rparr>) in
       foldr (\<lambda>(v,x) m. memory_update_untyped m v x) (zip pargs args) m)"

definition 
 "restore_locals x oldmem newmem =
  memory_update_untyped
  (Abs_memory (Rep_memory newmem \<lparr> mem_locals := mem_locals (Rep_memory oldmem) \<rparr>))
  x (memory_lookup_untyped newmem x)"

lemma restore_locals_lookup:  
 "memory_lookup_untyped (restore_locals x oldmem newmem) y =
  (if y=x then memory_lookup_untyped newmem y
   else if vu_global y then memory_lookup_untyped newmem y
   else memory_lookup_untyped oldmem y)"
using Abs_memory_inverse Rep_memory memory_lookup_untyped_def memory_lookup_update_untyped restore_locals_def by auto
*)

fun denotation_untyped :: "program_rep \<Rightarrow> denotation" where
  denotation_untyped_Seq: "denotation_untyped (Seq p1 p2) m = compose_distr (denotation_untyped p2) (denotation_untyped p1 m)"
| denotation_untyped_Assign: "denotation_untyped (Assign pat e) m = point_distr (memory_update_untyped_pattern m pat (eu_fun e m))"
| denotation_untyped_Sample: "denotation_untyped (Sample pat e) m = apply_to_distr (memory_update_untyped_pattern m pat) (ed_fun e m)"
| denotation_untyped_Skip: "denotation_untyped (Skip) m = point_distr m"
| denotation_untyped_IfTE: "denotation_untyped (IfTE e thn els) m = (if (eu_fun e m = embedding True) then denotation_untyped thn m else denotation_untyped els m)"
(* | denotation_untyped_While: "denotation_untyped (While e p) m = 
    Abs_distr (\<lambda>m'. real (\<Sum>n. ereal (Rep_distr (compose_distr (\<lambda>m. if eu_fun e m = embedding True then 0 else point_distr m)
                                            (while_iter n (\<lambda>m. eu_fun e m = embedding True) (denotation_untyped p) m)) m')))" *)
| denotation_untyped_While: "denotation_untyped (While e p) m =
  (SUP n. while_denotation_n n (\<lambda>m. eu_fun e m = embedding True) (denotation_untyped p) m)"
| denotation_untyped_CallProc: "denotation_untyped (CallProc v (Proc body pargs return) args) m = 
  (let argval = eu_fun args m in
  let m' = init_locals m in
  let m' = memory_update_untyped_pattern m' pargs argval in
  apply_to_distr (\<lambda>m'.
    let res = eu_fun return m' in
    let m' = restore_locals m m' in
    memory_update_untyped_pattern m' v res)
  (denotation_untyped body m'))"
(*  apply_to_distr (restore_locals v m)
  (apply_to_distr (\<lambda>m. memory_update_untyped_pattern m v (eu_fun return m))
  (denotation_untyped body (init_locals pargs args m)))" *)

(* New plan (written monadically):
  do
   let m_init = m
   let arg = "evaluate args in m" (arg is a single value now)
   let m = m[locals:=default]
   let m = memory_update_untyped_pattern m v arg
   m <- denotation_untyped body m
   let res = eu_fun return m
   let m = restore_locals m_init m
   let m = memory_update_untyped_pattern m v res
   return m
*)

| denotation_untyped_CallProc_bad: "denotation_untyped (CallProc v _ args) m = 0" (* Cannot happen for well-typed programs *)

definition "denotation prog = denotation_untyped (Rep_program prog)"

lemma denotation_untyped_assoc: "denotation_untyped (Seq (Seq x y) z) = denotation_untyped (Seq x (Seq y z))"
  unfolding denotation_untyped_Seq[THEN ext] 
  unfolding compose_distr_assoc ..

lemma denotation_Seq_Skip1 [simp]: "denotation_untyped (Seq Skip c) = denotation_untyped c"
  by auto
lemma denotation_Seq_Skip2 [simp]: "denotation_untyped (Seq c Skip) = denotation_untyped c"
  unfolding denotation_untyped_Seq[THEN ext] denotation_untyped_Skip[THEN ext] 
  by auto

lemma denotation_Halt [simp]: "denotation_untyped Halt = (\<lambda>m. 0)"
  apply (rule ext) unfolding Halt_def by simp

declare denotation_untyped_While[simp del]

lemma denotation_untyped_While_n: "denotation_untyped (While_n n e p) = while_denotation_n n (\<lambda>m. eu_fun e m = embedding True) (denotation_untyped p)"
    apply (induct_tac n) by auto


lemma mono_denotation_While_n: "mono (\<lambda>n. denotation_untyped (While_n n e p))"
  apply (rule mono_funI) unfolding denotation_untyped_While_n by (fact mono_while_denotation_n)

lemma denotation_untyped_While' [simp]: "denotation_untyped (While e p) =
  (SUP n. denotation_untyped (While_n n e p))"
proof -
  have "\<And>m. denotation_untyped (While e p) m = (SUP n. denotation_untyped (While_n n e p) m)"
    using denotation_untyped_While_n unfolding denotation_untyped_While by simp
  thus ?thesis by auto
qed

lemma denotation_While_n_diff: 
  "ennreal_Rep_distr (denotation_untyped (While_n n e p) m)
 + ennreal_Rep_distr (denotation_untyped (While_n_exact n e p) m)
 = ennreal_Rep_distr (denotation_untyped (While_n (Suc n) e p) m)"
proof (induction n arbitrary: m)
case 0
  show ?case by (auto simp: plus_fun_def)
next case (Suc n)
  show ?case
  proof (cases "eu_fun e m = embedding True")
  case True
    have "ennreal_Rep_distr (denotation_untyped (While_n (Suc n) e p) m) + ennreal_Rep_distr (denotation_untyped (While_n_exact (Suc n) e p) m)
        = ennreal_Rep_distr (compose_distr (denotation_untyped (While_n n e p)) (denotation_untyped p m)) +
          ennreal_Rep_distr (compose_distr (denotation_untyped (While_n_exact n e p)) (denotation_untyped p m))"
      using True by simp
    also have "\<dots> = ennreal_Rep_distr (compose_distr (denotation_untyped (While_n (Suc n) e p))
                                              (denotation_untyped p m))"
      apply (rule compose_distr_add_left)
      by (fact Suc.IH)
    also have "\<dots> = ennreal_Rep_distr (denotation_untyped (While_n (Suc (Suc n)) e p) m)"
      using True by simp
    finally show ?thesis by assumption
  next case False
    have "ennreal_Rep_distr (denotation_untyped (While_n (Suc n) e p) m) + ennreal_Rep_distr (denotation_untyped (While_n_exact (Suc n) e p) m)
        = ennreal_Rep_distr (point_distr m)"
      by (simp add: False plus_fun_def)
    also have "\<dots> = ennreal_Rep_distr (denotation_untyped (While_n (Suc (Suc n)) e p) m)"
      using False by simp
    finally show ?thesis by assumption
  qed 
qed


lemma denotation_untyped_While'': "ennreal_Rep_distr (denotation_untyped (While e p) m) m' =
  (\<Sum>n. ennreal_Rep_distr (denotation_untyped (While_n_exact n e p) m) m')"
proof -
  have "ennreal_Rep_distr (denotation_untyped (While e p) m) m' =
        (SUP n. ennreal_Rep_distr (denotation_untyped (While_n n e p) m) m')"
    apply (subst denotation_untyped_While')
    by (simp add: ennreal_Rep_SUP_distr mono_denotation_While_n[THEN mono_funD])
  also have "\<dots> = (SUP n. sum (\<lambda>n'. ennreal_Rep_distr (denotation_untyped (While_n_exact n' e p) m) m') {..<n})"
  proof -
    {fix n
    have "ennreal_Rep_distr (denotation_untyped (While_n n e p) m) m' =
          (\<Sum>n'<n. ennreal_Rep_distr (denotation_untyped (While_n_exact n' e p) m) m')"
      apply (induction n)
       close simp
      apply (subst denotation_While_n_diff[symmetric])
      unfolding plus_fun_def by simp}
    thus ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>n. ennreal_Rep_distr (denotation_untyped (While_n_exact n e p) m) m')"
    by (rule suminf_ennreal_eq_SUP[symmetric])
  finally show ?thesis by assumption
qed

lemma while_unfold_untyped: "denotation_untyped (While e p) = denotation_untyped (IfTE e (Seq p (While e p)) Skip)"
proof -
  have inc: "\<And>m m'. incseq (\<lambda>n. ennreal_Rep_distr (denotation_untyped (While_n n e p) m) m')"
    apply (rule mono_funD) apply (rule mono_apply[OF mono_ennreal_Rep_distr])
    apply (rule mono_funD) by (rule mono_denotation_While_n)
  have inc': "\<And>m. incseq (\<lambda>y. denotation_untyped (IfTE e (Seq p (While_n y e p)) Skip) m)" 
    apply (case_tac "eu_fun e m = embedding True")
     apply simp apply (rule mono_apply[OF mono_compose_distr1]) close (rule mono_denotation_While_n)
    by simp
  have inc3: "\<And>m. incseq (\<lambda>n. compose_distr (denotation_untyped (While_n n e p)) (denotation_untyped p m))" 
    apply (rule mono_apply[OF mono_compose_distr1]) by (rule mono_denotation_While_n)
  
  {fix m m'
  have "ennreal_Rep_distr (denotation_untyped (While e p) m) m' = ennreal_Rep_distr ((SUP n. denotation_untyped (While_n n e p)) m) m'"
    unfolding denotation_untyped_While' by simp
  also have "\<dots> = (SUP n. ennreal_Rep_distr (denotation_untyped (While_n n e p) m) m')"
    by (simp add: ennreal_Rep_SUP_distr mono_denotation_While_n[THEN mono_funD])
  also have "\<dots> = (SUP n. ennreal_Rep_distr (denotation_untyped (While_n (Suc n) e p) m) m')"
    apply (rule SUP_Suc) by (fact inc)
  also have "\<dots> = (SUP n. ennreal_Rep_distr (denotation_untyped (IfTE e (Seq p (While_n n e p)) Skip) m) m')"
    by simp
(*   also have "\<dots> = ennreal_Rep_distr ((SUP n. denotation_untyped (IfTE e (Seq p (While_n n e p)) Skip)) m) m'"
    unfolding SUP_apply apply (subst ereal_Rep_SUP_distr)
    using inc' by auto *)
  also have "\<dots> = (if eu_fun e m = embedding True 
                     then (SUP n. ennreal_Rep_distr (denotation_untyped (Seq p (While_n n e p)) m) m')  
                     else (ennreal_Rep_distr (denotation_untyped Skip m) m'))"
    by auto
  also have "\<dots> = (if eu_fun e m = embedding True 
                     then (SUP n. ennreal_Rep_distr (compose_distr (denotation_untyped (While_n n e p)) (denotation_untyped p m)) m')  
                     else (ennreal_Rep_distr (denotation_untyped Skip m) m'))"
    by auto
  also have "(SUP n. ennreal_Rep_distr (compose_distr (denotation_untyped (While_n n e p)) (denotation_untyped p m)) m')
            = (ennreal_Rep_distr (compose_distr (SUP n. denotation_untyped (While_n n e p)) (denotation_untyped p m)) m')"
    apply (subst compose_distr_SUP_left) close (fact mono_denotation_While_n)
    apply (subst ennreal_Rep_SUP_distr) close (fact inc3)
    by auto
  also have "(SUP n. denotation_untyped (While_n n e p)) = denotation_untyped (While e p)"
    by simp
  also have "(if eu_fun e m = embedding True 
      then ennreal_Rep_distr (compose_distr (denotation_untyped (While e p)) (denotation_untyped p m)) m'
      else ennreal_Rep_distr (denotation_untyped Skip m) m') 
      = ennreal_Rep_distr (denotation_untyped (IfTE e (Seq p (While e p)) Skip) m) m'"
    by simp
  finally have "ennreal_Rep_distr (denotation_untyped (While e p) m) m' = ennreal_Rep_distr (denotation_untyped (IfTE e (Seq p (While e p)) Skip) m) m'" 
    by assumption}
  thus ?thesis  
    apply (rule_tac ext) apply (rule ennreal_Rep_distr_inject[THEN iffD1]) by rule
qed

subsection {* Misc (free vars, lossless) *}

fun vars_untyped :: "program_rep \<Rightarrow> variable_untyped list" 
and vars_proc_untyped :: "procedure_rep \<Rightarrow> variable_untyped list" where
  "vars_untyped Skip = []"
| "vars_untyped (Seq p1 p2) = (vars_untyped p1) @ (vars_untyped p2)"
| "vars_untyped (Assign pat e) = pu_vars pat @ eu_vars e"
| "vars_untyped (Sample pat e) = pu_vars pat @ ed_vars e"
| "vars_untyped (IfTE e p1 p2) = eu_vars e @ vars_untyped p1 @ vars_untyped p2"
| "vars_untyped (While e p) = eu_vars e @ vars_untyped p"
| "vars_untyped (CallProc v proc args) = 
      pu_vars v @ eu_vars args @ vars_proc_untyped proc"
| "vars_proc_untyped (Proc body pargs return) =
      [v. v\<leftarrow>pu_vars pargs, vu_global v]
      @ [v. v\<leftarrow>vars_untyped body, vu_global v]
      @ [v. v\<leftarrow>eu_vars return, vu_global v]"
| "vars_proc_untyped (ProcRef i) = []"
| "vars_proc_untyped (ProcAppl p q) = (vars_proc_untyped p) @ (vars_proc_untyped q)"
| "vars_proc_untyped (ProcAbs p) = vars_proc_untyped p"
| "vars_proc_untyped (ProcPair p q) = vars_proc_untyped p @ vars_proc_untyped q"
| "vars_proc_untyped (ProcUnpair _ p) = vars_proc_untyped p"
| "vars_proc_untyped ProcUnit = []"

definition "vars prog = vars_untyped (Rep_program prog)"

fun write_vars_untyped :: "program_rep \<Rightarrow> variable_untyped list" 
and write_vars_proc_untyped :: "procedure_rep \<Rightarrow> variable_untyped list" where
  "write_vars_untyped Skip = []"
| "write_vars_untyped (Seq p1 p2) = (write_vars_untyped p1) @ (write_vars_untyped p2)"
| "write_vars_untyped (Assign pat e) = pu_vars pat"
| "write_vars_untyped (Sample pat e) = pu_vars pat"
| "write_vars_untyped (IfTE e p1 p2) = write_vars_untyped p1 @ write_vars_untyped p2"
| "write_vars_untyped (While e p) = write_vars_untyped p"
| "write_vars_untyped (CallProc v prc args) = 
      pu_vars v @ write_vars_proc_untyped prc"
| "write_vars_proc_untyped (Proc body pargs ret) =
      [v. v\<leftarrow>pu_vars pargs, vu_global v]
      @ [v. v\<leftarrow>write_vars_untyped body, vu_global v]"
| "write_vars_proc_untyped (ProcRef i) = []"
| "write_vars_proc_untyped (ProcAppl p q) = (write_vars_proc_untyped p) @ (write_vars_proc_untyped q)"
| "write_vars_proc_untyped (ProcAbs p) = write_vars_proc_untyped p"
| "write_vars_proc_untyped (ProcPair p q) = write_vars_proc_untyped p @ write_vars_proc_untyped q"
| "write_vars_proc_untyped (ProcUnpair _ p) = write_vars_proc_untyped p"
| "write_vars_proc_untyped ProcUnit = []"
definition "write_vars prog = write_vars_untyped (Rep_program prog)"

lemma write_vars_subset_vars_untyped: 
  shows "set (write_vars_untyped p) \<subseteq> set (vars_untyped p)"
    and "set (write_vars_proc_untyped q) \<subseteq> set (vars_proc_untyped q)"
  apply (induct p and q) by auto 

definition "lossless_untyped p = (\<forall>m. weight_distr (denotation_untyped p m) = 1)"
definition "lossless p = (\<forall>m. weight_distr (denotation p m) = 1)"


definition "local_vars prog = filter (\<lambda>x. \<not>vu_global x) (vars prog)"

lemma vars_proc_untyped_global: "x\<in>set(vars_proc_untyped q) \<Longrightarrow> vu_global x"
proof -
  define p where "p == undefined :: program_rep"
  have True and "x\<in>set(vars_proc_untyped q) \<Longrightarrow> vu_global x"
    by (induct p and q, auto)
  thus "x\<in>set(vars_proc_untyped q) \<Longrightarrow> vu_global x" by simp
qed

subsection {* Variables renaming *}

definition "rename_variables_pattern f p = Abs_pattern_untyped
  \<lparr> pur_var_getters=map (apfst f) (pu_var_getters p), pur_type=pu_type p \<rparr>"
lemma Rep_rename_variables_pattern:
  assumes "\<And>x. vu_type (f x) = vu_type x"
  shows "Rep_pattern_untyped (rename_variables_pattern f p) = 
         \<lparr> pur_var_getters=map (apfst f) (pu_var_getters p), pur_type=pu_type p \<rparr>"
  unfolding rename_variables_pattern_def
  apply (subst Abs_pattern_untyped_inverse) apply auto
  using Rep_pattern_untyped assms unfolding pu_var_getters_def pu_type_def by fastforce+
  
lemma pu_var_getters_rename_variables_pattern:
  assumes "\<And>x. vu_type (f x) = vu_type x"
  shows "pu_var_getters (rename_variables_pattern f p) = map (apfst f) (pu_var_getters p)"
apply (subst pu_var_getters_def)
apply (subst Rep_rename_variables_pattern) close (fact assms)
by auto

lemma pu_vars_rename_variables_pattern:
  assumes "\<And>x. vu_type (f x) = vu_type x"
  shows "pu_vars (rename_variables_pattern f p) = map f (pu_vars p)"
unfolding pu_vars_def
apply (subst pu_var_getters_rename_variables_pattern[OF assms])
by simp



definition rename_variables_memory where
  "rename_variables_memory f m = Abs_memory (\<lambda>x. Rep_memory m (f x))"
lemma Rep_rename_variables_memory: 
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  shows "Rep_memory (rename_variables_memory f m) = (\<lambda>x. Rep_memory m (f x))"
    unfolding rename_variables_memory_def 
    apply (subst Abs_memory_inverse, auto)
    by (metis (no_types, lifting) Rep_memory mem_Collect_eq type)

lemma lookup_rename_variables_memory: 
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  shows "memory_lookup_untyped (rename_variables_memory f m) v = memory_lookup_untyped m (f v)"
unfolding Rep_rename_variables_memory[OF type] global by simp

definition "rename_variables_expression f e = Abs_expression_untyped 
  \<lparr> eur_fun=(\<lambda>m. eu_fun e (rename_variables_memory f m)), eur_type=eu_type e, eur_vars=map f (eu_vars e) \<rparr>"
lemma Rep_rename_variables_expression [simp]:  
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  shows "Rep_expression_untyped (rename_variables_expression f e) =
    \<lparr> eur_fun=(\<lambda> m. eu_fun e (rename_variables_memory f m)), eur_type=eu_type e, eur_vars=map f (eu_vars e) \<rparr>"
proof -
  have t: "\<And>m1 m2. \<forall>v\<in>set (eu_vars e). memory_lookup_untyped m1 (f v) = memory_lookup_untyped m2 (f v) \<Longrightarrow>
             eu_fun e (rename_variables_memory f m1) = eu_fun e (rename_variables_memory f m2)"
  proof -
    fix m1 m2
    assume "\<forall>v\<in>set (eu_vars e). memory_lookup_untyped m1 (f v) = memory_lookup_untyped m2 (f v)"
    hence  "\<forall>v\<in>set (eu_vars e). memory_lookup_untyped (rename_variables_memory f m1) v 
                              = memory_lookup_untyped (rename_variables_memory f m2) v"
      unfolding lookup_rename_variables_memory[OF type, OF global].
    thus "?thesis m1 m2"
      using eu_fun_footprint by blast
  qed

  show ?thesis
    unfolding rename_variables_expression_def apply (subst Abs_expression_untyped_inverse, auto)
    using t by simp
qed

lemma eu_vars_rename_variables_expression: 
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  shows "eu_vars (rename_variables_expression f e) = map f (eu_vars e)"
apply (subst eu_vars_def)
apply (subst Rep_rename_variables_expression)
using assms by simp_all


lemma eu_fun_rename_variables_expression: 
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  shows "eu_fun (rename_variables_expression f e) = (\<lambda> m. eu_fun e (rename_variables_memory f m))"
apply (subst eu_fun_def)
apply (subst Rep_rename_variables_expression)
using assms by simp_all


definition "rename_variables_expression_distr f e = Abs_expression_distr 
  \<lparr> edr_fun=(\<lambda>m. ed_fun e (rename_variables_memory f m)), edr_type=ed_type e, edr_vars=map f (ed_vars e) \<rparr>"
lemma Rep_rename_variables_expression_distr:  
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  shows "Rep_expression_distr (rename_variables_expression_distr f e) =
    \<lparr> edr_fun=(\<lambda>m. ed_fun e (rename_variables_memory f m)), edr_type=ed_type e, edr_vars=map f (ed_vars e) \<rparr>"
proof -
  have t: "\<And>m1 m2. \<forall>v\<in>set (ed_vars e). memory_lookup_untyped m1 (f v) = memory_lookup_untyped m2 (f v) \<Longrightarrow>
             ed_fun e (rename_variables_memory f m1) = ed_fun e (rename_variables_memory f m2)"
  proof -
    fix m1 m2
    assume "\<forall>v\<in>set (ed_vars e). memory_lookup_untyped m1 (f v) = memory_lookup_untyped m2 (f v)"
    hence  "\<forall>v\<in>set (ed_vars e). memory_lookup_untyped (rename_variables_memory f m1) v 
                              = memory_lookup_untyped (rename_variables_memory f m2) v"
      unfolding lookup_rename_variables_memory[OF type, OF global].                          
    thus "?thesis m1 m2"
      using ed_fun_footprint by blast
  qed

  show ?thesis
    unfolding rename_variables_expression_distr_def apply (subst Abs_expression_distr_inverse, auto)
    using Rep_expression_distr ed_fun_def ed_type_def close auto
    using t by simp
qed

lemma ed_vars_rename_variables_expression_distr: 
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  shows "ed_vars (rename_variables_expression_distr f e) = map f (ed_vars e)"
apply (subst ed_vars_def)
apply (subst Rep_rename_variables_expression_distr)
using assms by simp_all

lemma ed_fun_rename_variables_expression_distr: 
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  shows "ed_fun (rename_variables_expression_distr f e) = (\<lambda> m. ed_fun e (rename_variables_memory f m))"
apply (subst ed_fun_def)
apply (subst Rep_rename_variables_expression_distr)
using assms by simp_all


(* Note: does not rename recursively within procedures *)
fun rename_variables where
  "rename_variables f (Assign x e) = Assign (rename_variables_pattern f x) (rename_variables_expression f e)"
| "rename_variables f (Sample x e) = Sample (rename_variables_pattern f x) (rename_variables_expression_distr f e)"
| "rename_variables f Skip = Skip"
| "rename_variables f (Seq p1 p2) = Seq (rename_variables f p1) (rename_variables f p2)"
| "rename_variables f (IfTE c p1 p2) = IfTE (rename_variables_expression f c) (rename_variables f p1) (rename_variables f p2)"
| "rename_variables f (While c p) = While (rename_variables_expression f c) (rename_variables f p)"
| "rename_variables f (CallProc x p e) = CallProc (rename_variables_pattern f x) p (rename_variables_expression f e)"

lemma rename_variables_memory_id:
  shows "rename_variables_memory id m = m"
  apply (subst Rep_memory_inject[symmetric])
  apply (subst Rep_rename_variables_memory) 
  unfolding id_def by auto

lemma rename_variables_pattern_id: 
  shows "rename_variables_pattern id p = p" 
  unfolding id_def
  apply (subst Rep_pattern_untyped_inject[symmetric])
  apply (subst Rep_rename_variables_pattern, auto)
  unfolding pu_var_getters_def pu_type_def apfst_def id_def
  by(cases "Rep_pattern_untyped p", auto)
 
lemma rename_variables_expression_id: "rename_variables_expression id p = p" 
  apply (subst Rep_expression_untyped_inject[symmetric])
  apply (subst Rep_rename_variables_expression, auto)
  apply (subst rename_variables_memory_id)
  unfolding eu_fun_def eu_type_def eu_vars_def by auto

lemma rename_variables_expression_distr_id: "rename_variables_expression_distr id p = p" 
  apply (subst Rep_expression_distr_inject[symmetric])
  apply (subst Rep_rename_variables_expression_distr, auto)
  apply (subst rename_variables_memory_id)
  unfolding ed_fun_def ed_type_def ed_vars_def by auto

lemma rename_variables_id: "rename_variables id p = p" 
  apply (induct p)
  by (auto simp: id_def rename_variables_pattern_id[unfolded id_def] 
        rename_variables_expression_id[unfolded id_def] rename_variables_expression_distr_id[unfolded id_def])


lemma rename_variables_memory_compose:
  assumes type1: "\<And>x. vu_type (f1 x) = vu_type x"
  assumes type2: "\<And>x. vu_type (f2 x) = vu_type x"
  shows "rename_variables_memory f2 (rename_variables_memory f1 p) = rename_variables_memory (f1 o f2) p"
  apply (subst Rep_memory_inject[symmetric])
  apply (subst Rep_rename_variables_memory) close (fact type2)
  apply (subst Rep_rename_variables_memory) using type1 type2 o_def close simp
  apply (subst Rep_rename_variables_memory) using type1 type2 o_def close simp
  by simp

lemma rename_variables_pattern_compose: 
  assumes type1: "\<And>x. vu_type (f1 x) = vu_type x"
  assumes type2: "\<And>x. vu_type (f2 x) = vu_type x"
  shows "rename_variables_pattern f2 (rename_variables_pattern f1 p) = rename_variables_pattern (f2 o f1) p"
  apply (subst Rep_pattern_untyped_inject[symmetric])
  apply (subst Rep_rename_variables_pattern) close (fact type2)
  apply (subst Rep_rename_variables_pattern) using type1 type2 o_def close simp
  unfolding pu_var_getters_def
  apply (subst Rep_rename_variables_pattern) close (fact type1)
  apply (auto simp: apfst_def map_prod.comp pu_var_getters_def)
  by (simp add: Rep_rename_variables_pattern pu_type_def type1)

lemma rename_variables_expression_memory:
  assumes surj_f: "surj f"
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  shows "eu_fun (rename_variables_expression (inv f) e) (rename_variables_memory f m) = eu_fun e m"
proof -
  have type': "\<And>x. vu_type (inv f x) = vu_type x"
    by (metis surj_f surj_f_inv_f type)
  have global': "\<And>x. vu_global (inv f x) = vu_global x"
    by (metis surj_f surj_f_inv_f global)
  have id: "f o inv f = id"
    using surj_f surj_iff by blast
  show ?thesis
    unfolding eu_fun_def
    apply (subst Rep_rename_variables_expression) close (fact type') close (fact global')
    apply simp
    apply (subst rename_variables_memory_compose) close (fact type) close (fact type')
    unfolding id eu_fun_def apply (subst rename_variables_memory_id) ..
qed

lemma rename_variables_expression_distr_memory:
  assumes surj_f: "surj f"
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  shows "ed_fun (rename_variables_expression_distr (inv f) e) (rename_variables_memory f m) = ed_fun e m"
proof -
  have type': "\<And>x. vu_type (inv f x) = vu_type x"
    by (metis surj_f surj_f_inv_f type)
  have global': "\<And>x. vu_global (inv f x) = vu_global x"
    by (metis surj_f surj_f_inv_f global)
  have id: "f o inv f = id"
    using surj_f surj_iff by blast
  show ?thesis
    unfolding ed_fun_def
    apply (subst Rep_rename_variables_expression_distr) close (fact type') close (fact global')
    apply simp
    apply (subst rename_variables_memory_compose) close (fact type) close (fact type')
    unfolding id ed_fun_def apply (subst rename_variables_memory_id) ..
qed

lemma rename_variables_expression_compose: 
  assumes type1: "\<And>x. vu_type (f1 x) = vu_type x"
  assumes global1: "\<And>x. vu_global (f1 x) = vu_global x"
  assumes type2: "\<And>x. vu_type (f2 x) = vu_type x"
  assumes global2: "\<And>x. vu_global (f2 x) = vu_global x"
  shows "rename_variables_expression f2 (rename_variables_expression f1 p) = rename_variables_expression (f2 o f1) p"
  apply (subst Rep_expression_untyped_inject[symmetric])
  apply (subst Rep_rename_variables_expression) close (fact type2) close (fact global2)
  apply (subst Rep_rename_variables_expression) using type1 type2 o_def close auto using global1 global2 o_def close auto
  apply (subst rename_variables_memory_compose[symmetric]) close (fact type2) close (fact type1)
  apply auto
  close (simp add: eu_fun_def global1 type1)
  close (simp add: eu_type_def global1 type1)
  unfolding eu_vars_def
  apply (subst Rep_rename_variables_expression) close (fact type1) close (fact global1)
  unfolding eu_vars_def by auto
  
lemma rename_variables_expression_distr_compose:
  assumes type1: "\<And>x. vu_type (f1 x) = vu_type x"
  assumes global1: "\<And>x. vu_global (f1 x) = vu_global x"
  assumes type2: "\<And>x. vu_type (f2 x) = vu_type x"
  assumes global2: "\<And>x. vu_global (f2 x) = vu_global x"
  shows "rename_variables_expression_distr f2 (rename_variables_expression_distr f1 p) = rename_variables_expression_distr (f2 o f1) p"
  apply (subst Rep_expression_distr_inject[symmetric])
  apply (subst Rep_rename_variables_expression_distr) close (fact type2) close (fact global2)
  apply (subst Rep_rename_variables_expression_distr) using type1 type2 o_def close auto using global1 global2 o_def close auto
  apply (subst rename_variables_memory_compose[symmetric]) close (fact type2) close (fact type1)
  apply auto
  close (simp add: Rep_rename_variables_expression_distr ed_fun_def global1 type1)
  close (simp add: Rep_rename_variables_expression_distr ed_type_def global1 type1)
  unfolding ed_vars_def
  apply (subst Rep_rename_variables_expression_distr) close (fact type1) close (fact global1)
  unfolding ed_vars_def by auto

lemma rename_variables_compose:
  assumes type1: "\<And>x. vu_type (f1 x) = vu_type x"
  assumes global1: "\<And>x. vu_global (f1 x) = vu_global x"
  assumes type2: "\<And>x. vu_type (f2 x) = vu_type x"
  assumes global2: "\<And>x. vu_global (f2 x) = vu_global x"
  shows "rename_variables f2 (rename_variables f1 p) = rename_variables (f2 o f1) p"
  apply (induct p)
  by (auto simp: o_def rename_variables_pattern_compose[OF type1, OF type2] 
        rename_variables_expression_compose[OF type1, OF global1, OF type2, OF global2]
        rename_variables_expression_distr_compose[OF type1, OF global1, OF type2, OF global2])

lemma update_rename_variables_memory:
  assumes bij_f: "bij f"
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  shows "memory_update_untyped (rename_variables_memory f m) x a = rename_variables_memory f (memory_update_untyped m (f x) a)"
proof -
  have bij_rw: "\<And>x y. f x = f y == x = y" using bij_f
    by (smt bij_pointE)
    
  show ?thesis
  apply (subst Rep_memory_inject[symmetric])
  unfolding Rep_memory_update_untyped' Rep_rename_variables_memory[OF type]
  using bij_rw type by auto
qed

lemma update_pattern_rename_variables_memory:
  assumes bij_f: "bij f"
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  shows "memory_update_untyped_pattern (rename_variables_memory f m) x a
       = rename_variables_memory f (memory_update_untyped_pattern m (rename_variables_pattern f x) a)"
proof -
  define pvg where "pvg == pu_var_getters x"
  have "foldl (\<lambda>m (v, f). memory_update_untyped m v (f a)) (rename_variables_memory f m) pvg =
    rename_variables_memory f (foldl (\<lambda>m (v, f). memory_update_untyped m v (f a)) m (map (apfst f) pvg))"
    apply (induct pvg rule:rev_induct)
     close simp
    apply auto
    apply (subst update_rename_variables_memory)
      using bij_f close assumption
     using type close assumption
    by auto
  thus ?thesis
    unfolding memory_update_untyped_pattern_def
    apply (subst pu_var_getters_rename_variables_pattern)
     using type pvg_def by auto
qed


lemma rename_variables_restore_locals:   
  assumes fix_globals: "\<And>x. vu_global x \<Longrightarrow> f x = x"
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  shows "rename_variables_memory f (restore_locals old new) = restore_locals (rename_variables_memory f old) new"
    apply (subst Rep_memory_inject[symmetric])
    unfolding Rep_rename_variables_memory[OF type] Rep_restore_locals
    using fix_globals global by auto

lemma rename_variables_restore_locals_new:
  assumes fix_globals: "\<And>x. vu_global x \<Longrightarrow> f x = x"
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  shows "restore_locals old (rename_variables_memory f new) = restore_locals old new"
    apply (subst Rep_memory_inject[symmetric])
    unfolding Rep_rename_variables_memory[OF type] Rep_restore_locals
    using fix_globals by auto

lemma rename_variables_init_locals:
  assumes fix_globals: "\<And>x. vu_global x \<Longrightarrow> f x = x"
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  shows "init_locals (rename_variables_memory f m) = init_locals m"
    apply (subst Rep_memory_inject[symmetric])
    unfolding Rep_rename_variables_memory[OF type] Rep_init_locals
    using fix_globals Rep_memory by auto    

lemma rename_variables_init_locals_outside:
  assumes fix_globals: "\<And>x. vu_global x \<Longrightarrow> f x = x"
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  shows "rename_variables_memory f (init_locals m) = init_locals m"
proof -
  {fix x
  have "(if vu_global (f x) then Rep_memory m (f x) else t_default (vu_type (f x))) =
           (if vu_global x then Rep_memory m x else t_default (vu_type x))"
  proof (cases "vu_global x")
  case True
    hence gl_fx: "vu_global (f x)" using global by simp
    show "?thesis"
      using gl_fx True fix_globals by simp
  next case False
    hence lo_fx: "\<not> vu_global (f x)" using global by simp
    show ?thesis
      using lo_fx False type by simp
  qed}
  thus ?thesis
    apply (subst Rep_memory_inject[symmetric])
    unfolding Rep_rename_variables_memory[OF type] Rep_init_locals
    by auto    
qed

lemma denotation_rename_variables:
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes fix_global: "\<And>x. vu_global x \<Longrightarrow> f x = x"
  assumes bij_f: "bij f" 
  shows "denotation_untyped (rename_variables f p) m = 
         apply_to_distr (rename_variables_memory (inv f)) (denotation_untyped p (rename_variables_memory f m))"
    (is "?P p m")
proof -
  from bij_f have "inj f" by (simp add: bij_betw_def)
  from bij_f have "surj f" by (simp add: bij_betw_def) 
  from bij_f have "bij (inv f)" by (simp add: bij_betw_inv_into)
  from `inj f` have inv_f_f: "inv f o f = id" by simp
  from `surj f` have f_inv_f: "f o inv f = id" using surj_iff by auto 

  have global: "\<And>x. vu_global (f x) = vu_global x" using fix_global by (metis `inj f` inv_f_eq)
  
  from type have type': "\<And>x. vu_type (inv f x) = vu_type x"
    by (metis `surj f` surj_f_inv_f)
  from global have global': "\<And>x. vu_global (inv f x) = vu_global x"
    by (metis `surj f` surj_f_inv_f)
  from fix_global have fix_global': "\<And>x. vu_global x \<Longrightarrow> inv f x = x"
    by (simp add: fix_global `inj f` inv_f_eq)

  have ren_f_inv_f: "\<And>a. rename_variables_memory f (rename_variables_memory (inv f) a) = a"
    by (simp add: inv_f_f rename_variables_memory_compose rename_variables_memory_id type type')
  have ren_inv_f_f: "\<And>a. rename_variables_memory (inv f) (rename_variables_memory f a) = a"
    by (simp add: f_inv_f rename_variables_memory_compose rename_variables_memory_id type type')
  from ren_f_inv_f ren_inv_f_f have ind: "\<And>a m'. indicator {rename_variables_memory (inv f) a} m' = indicator {rename_variables_memory f m'} a"
    unfolding indicator_def by auto

  define p' where "p' == rename_variables f p"
  have "denotation_untyped p' m = 
    apply_to_distr (rename_variables_memory (inv f)) (denotation_untyped (rename_variables (inv f) p') (rename_variables_memory f m))"
  proof (induct p' arbitrary: m rule:program_rep.induct[of _ "\<lambda>p. True"])
    case Assign show ?case 
                  apply (simp add: )
                  apply (subst update_pattern_rename_variables_memory[OF `bij f` type global])
                  unfolding rename_variables_memory_compose[OF type type'] f_inv_f rename_variables_memory_id
                            rename_variables_pattern_compose[OF type' type]
                            rename_variables_expression_memory[OF `surj f` type global]
                            rename_variables_pattern_id ..
    next case Sample show ?case
                  apply (simp add: )
                  apply (subst update_pattern_rename_variables_memory[OF `bij f` type global])
                  unfolding rename_variables_memory_compose[OF type type'] f_inv_f rename_variables_memory_id
                            rename_variables_pattern_compose[OF type' type]
                            rename_variables_expression_distr_memory[OF `surj f` type global]
                            rename_variables_pattern_id ..
    next case Skip thus ?case 
                      apply (simp add: ) apply (subst rename_variables_memory_compose) close (fact type) close (fact type')
                      unfolding `f o inv f = id` apply (subst rename_variables_memory_id)..
    next case (Seq p1 p2)
      show ?case
        apply (simp add: )
        unfolding Seq.hyps[THEN ext]
        unfolding compose_distr_apply_to_distr apply_to_distr_compose_distr
        unfolding o_def rename_variables_memory_compose[OF type' type]
        unfolding inv_f_f[unfolded o_def] rename_variables_memory_id
        by simp
    next case (While e p m)
      {fix n
      have "while_denotation_n n (\<lambda>m. eu_fun e m = embedding True) (denotation_untyped p) m
          = apply_to_distr (rename_variables_memory (inv f))
             (while_denotation_n n (\<lambda>m. eu_fun (rename_variables_expression (inv f) e) m = embedding True)
                (denotation_untyped (rename_variables (inv f) p)) (rename_variables_memory f m))"
      proof (induct n arbitrary: m)
      case 0 show ?case by simp
      next case (Suc n)
        show ?case 
        proof (cases "eu_fun e m = embedding True") 
          case False
            hence "eu_fun (rename_variables_expression (inv f) e) (rename_variables_memory f m) \<noteq> embedding True"
              by (simp add: `surj f` global rename_variables_expression_memory type)
            with False show ?thesis by (simp add: ren_inv_f_f)
          next case True 
            let ?invfmem = "rename_variables_memory (inv f)"
            let ?invfexp = "rename_variables_expression (inv f)"
            let ?fmem = "rename_variables_memory f"
            let ?invf = "rename_variables (inv f)"
            let ?p = "denotation_untyped p"
            let ?pf = "denotation_untyped (?invf p)"
            let ?e = "\<lambda>m. eu_fun e m = embedding True"
            let ?ef = "\<lambda>m. eu_fun (?invfexp e) m = embedding True"
            from True have True': "?ef (?fmem m)"
              by (simp add: `surj f` global rename_variables_expression_memory type)

            have "while_denotation_n (Suc n) ?e ?p m
                = compose_distr (while_denotation_n n ?e ?p) (?p m)"
              using True by simp
            also have "\<dots> = compose_distr (\<lambda>m. apply_to_distr ?invfmem (while_denotation_n n ?ef ?pf (?fmem m))) (?p m)"
              using Suc by metis
            also have "\<dots> = apply_to_distr ?invfmem (compose_distr (\<lambda>m. while_denotation_n n ?ef ?pf (?fmem m)) (?p m))"
              apply (subst apply_to_distr_compose_distr[symmetric]) by rule
            also have "\<dots> = apply_to_distr ?invfmem (compose_distr (\<lambda>m. while_denotation_n n ?ef ?pf m) (apply_to_distr ?fmem (?p m)))"
              by (smt compose_distr_assoc compose_distr_cong compose_point_distr_l compose_point_distr_r)
            also have "\<dots> = apply_to_distr ?invfmem (compose_distr (\<lambda>m. while_denotation_n n ?ef ?pf m) (?pf (?fmem m)))"
              using While.hyps ren_f_inv_f by auto
            also have "\<dots> = apply_to_distr ?invfmem (while_denotation_n (Suc n) ?ef ?pf (?fmem m))"
              using True' by simp
            finally show ?thesis by assumption
        qed
      qed}
      note n_steps = this
      show ?case
        apply (simp del: denotation_untyped_While' add: denotation_untyped_While)
        apply (subst apply_to_distr_sup)
         close (fact mono_while_denotation_n)
        by (subst n_steps, rule)
    next case (IfTE e p1 p2 m)
      show ?case
        apply (subst ennreal_Rep_distr_inject[symmetric], rule ext, rename_tac m')
      proof (cases "eu_fun e m = embedding True")
        fix m'
        assume True1: "eu_fun e m = embedding True"
        hence True2: "eu_fun (rename_variables_expression (inv f) e) (rename_variables_memory f m) = embedding True"
          by (simp add: `surj f` global rename_variables_expression_memory type)
        show "(ennreal_Rep_distr (denotation_untyped (IfTE e p1 p2) m) m') =
          (ennreal_Rep_distr (apply_to_distr (rename_variables_memory (inv f))
          (denotation_untyped (rename_variables (inv f) (IfTE e p1 p2)) (rename_variables_memory f m))) m')"
          apply (simp add: ennreal_Rep_apply_to_distr True1 True2)
          apply (subst ind)
          apply (subst nn_integral_singleton_indicator_countspace)
          apply auto
          apply (subst ennreal_Rep_apply_distr_biject[where f="rename_variables_memory (inv f)" and g="rename_variables_memory f", symmetric])
            close (fact ren_inv_f_f) close (fact ren_f_inv_f)
          by (simp add: IfTE.hyps(1))
      next
        fix m'
        assume False1: "eu_fun e m \<noteq> embedding True"
        hence False2: "eu_fun (rename_variables_expression (inv f) e) (rename_variables_memory f m) \<noteq> embedding True"
          by (simp add: `surj f` global rename_variables_expression_memory type)
        show "ennreal_Rep_distr (denotation_untyped (IfTE e p1 p2) m) m' =
          ennreal_Rep_distr (apply_to_distr (rename_variables_memory (inv f))
          (denotation_untyped (rename_variables (inv f) (IfTE e p1 p2)) (rename_variables_memory f m))) m'"
          apply (simp add: ennreal_Rep_apply_to_distr False1 False2)
          apply (subst ind)
          apply (subst nn_integral_singleton_indicator_countspace)
          apply auto
          apply (subst ennreal_Rep_apply_distr_biject[where f="rename_variables_memory (inv f)" and g="rename_variables_memory f", symmetric])
            close (fact ren_inv_f_f) close (fact ren_f_inv_f)
          by (simp add: IfTE.hyps(2))
      qed
    next case (CallProc x p a) 
           show ?case proof (cases "\<exists>body pargs ret. p=Proc body pargs ret")
             case False
               have "denotation_untyped (CallProc x p a) m = 0"
                 apply (cases p) using False by (auto simp: )
               also have "denotation_untyped (rename_variables (inv f) (CallProc x p a)) (rename_variables_memory f m) = 0" 
                 apply (cases p) using False by (auto simp: )
               hence "apply_to_distr (rename_variables_memory (inv f))
                  (denotation_untyped (rename_variables (inv f) (CallProc x p a)) (rename_variables_memory f m)) = 0"
                    by simp
               finally show ?thesis by simp
             next case True 
               then obtain body pargs ret where p: "p=Proc body pargs ret" by auto
               show ?thesis
                 unfolding p
                 apply (simp add: )
                 apply (subst update_pattern_rename_variables_memory[OF `bij (inv f)` type' global', symmetric])
                 apply (subst rename_variables_expression_memory[OF `surj f` type global])
                 apply (subst rename_variables_restore_locals[OF fix_global' type' global']) close simp
                 apply (subst rename_variables_memory_compose[OF type type'])
                 unfolding f_inv_f
                 apply (subst rename_variables_memory_id)
                 apply (subst rename_variables_init_locals[OF fix_global type]) by auto
           qed
  qed auto
  thus ?thesis
    unfolding p'_def 
              rename_variables_compose[OF type, OF global, OF type', OF global']
              `inv f o f = id` rename_variables_id.
qed

fun rename_variables_proc where
  "rename_variables_proc f (Proc body args ret) = Proc (rename_variables f body) (rename_variables_pattern f args) (rename_variables_expression f ret)"
| "rename_variables_proc f (ProcRef i) = ProcRef i"
| "rename_variables_proc f (ProcAbs p) = ProcAbs (rename_variables_proc f p)"
| "rename_variables_proc f (ProcPair p1 p2) = ProcPair (rename_variables_proc f p1) (rename_variables_proc f p2)"
| "rename_variables_proc f (ProcUnpair b p) = ProcUnpair b (rename_variables_proc f p)"
| "rename_variables_proc f (ProcAppl p1 p2) = ProcAppl (rename_variables_proc f p1) (rename_variables_proc f p2)"
| "rename_variables_proc f ProcUnit = ProcUnit"

lemma rename_variables_proc_id: "rename_variables_proc id p = p" 
  apply (induct p)
  by (auto simp: id_def rename_variables_pattern_id[unfolded id_def] 
        rename_variables_expression_id[unfolded id_def] rename_variables_expression_distr_id[unfolded id_def])


lemma denotation_rename_variables_proc:
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  assumes fix_global: "\<And>x. vu_global x \<Longrightarrow> f x = x"
  assumes bijf: "bij f"
  shows "denotation_untyped (CallProc x (rename_variables_proc f p) a) = denotation_untyped (CallProc x p a)"
proof (rule ext, cases "\<exists>body pargs ret. p=Proc body pargs ret")
case False
  fix m
  have "denotation_untyped (CallProc x p a) m = 0"
    apply (cases p) using False by (auto simp: )
  also have "denotation_untyped (CallProc x (rename_variables_proc f p) a) m = 0"  
    apply (cases p) using False by (auto simp: )
  finally show "denotation_untyped (CallProc x (rename_variables_proc f p) a) m = denotation_untyped (CallProc x p a) m" by simp
next case True 
  then obtain body pargs ret where p: "p=Proc body pargs ret" by auto
  fix m
  have "surj f" using bijf bij_betw_imp_surj by auto
  have "bij (inv f)" by (simp add: `bij f` bij_imp_bij_inv) 
  have type': "\<And>x. vu_type (inv f x) = vu_type x" by (metis `surj f` surj_f_inv_f type)
  have global': "\<And>x. vu_global (inv f x) = vu_global x" by (metis `surj f` global surj_f_inv_f)
  have fix_global': "\<And>x. vu_global x \<Longrightarrow> inv f x = x" by (metis `bij f` bij_def fix_global inv_f_eq) 
  have inv_inv_f: "inv (inv f) = f" by (simp add: `bij f` inv_inv_eq)
  have "surj (inv f)" by (simp add: `bij (inv f)` bij_is_surj)
  show "denotation_untyped (CallProc x (rename_variables_proc f p) a) m = denotation_untyped (CallProc x p a) m" 
    unfolding p apply (simp add: ) 
    apply (subst denotation_rename_variables[OF type fix_global `bij f`], assumption)
    apply (subst apply_to_distr_twice)
    apply (subst rename_variables_restore_locals_new[OF fix_global' type'], assumption)
    apply (subst rename_variables_expression_memory[where f="inv f", unfolded inv_inv_f, OF `surj (inv f)` type' global'])
    apply (subst update_pattern_rename_variables_memory[symmetric, OF `bij f` type global])
    apply (subst rename_variables_init_locals_outside[OF fix_global type global], assumption)
    ..
qed

lemma pu_type_rename_variables:
  assumes "\<And>x. vu_type (f x) = vu_type x" 
  shows "pu_type (rename_variables_pattern f x) = pu_type x"
unfolding pu_type_def Rep_rename_variables_pattern[OF assms] by simp

lemma eu_type_rename_variables:
  assumes type: "\<And>x. vu_type (f x) = vu_type x" 
  assumes global: "\<And>x. vu_global (f x) = vu_global x" 
  shows "eu_type (rename_variables_expression f e) = eu_type e"
unfolding eu_type_def Rep_rename_variables_expression[OF assms] by simp

lemma ed_type_rename_variables:
  assumes type: "\<And>x. vu_type (f x) = vu_type x" 
  assumes global: "\<And>x. vu_global (f x) = vu_global x" 
  shows "ed_type (rename_variables_expression_distr f e) = ed_type e"
unfolding ed_type_def Rep_rename_variables_expression_distr[OF assms] by simp


lemma well_typed_rename_variables:
  assumes type: "\<And>x. vu_type (f x) = vu_type x"
  assumes global: "\<And>x. vu_global (f x) = vu_global x"
  assumes wt: "well_typed p"
  shows "well_typed (rename_variables f p)"
proof -
  define q where "q == undefined :: procedure_rep"
  have ?thesis and True
    using wt proof (induct p and q)
    case Assign thus ?case 
      apply auto apply (subst pu_type_rename_variables[OF type])
      by (subst eu_type_rename_variables[OF type global])
    next case Sample thus ?case 
      apply auto apply (subst pu_type_rename_variables[OF type])
      by (subst ed_type_rename_variables[OF type global])
    next case While thus ?case
      apply auto by (subst eu_type_rename_variables[OF type global])
    next case IfTE thus ?case
      apply auto by (subst eu_type_rename_variables[OF type global])
    next case (CallProc x p e) 
      from CallProc.prems obtain body pargs ret where p: "p = Proc body pargs ret"
        by (cases p, auto)
      from CallProc.prems show ?case
        unfolding p apply simp
      apply auto apply (subst pu_type_rename_variables[OF type], assumption)
      by (subst eu_type_rename_variables[OF type global])
    next case Seq thus ?case by auto
    next case Skip show ?case by auto
    qed simp_all
  thus ?thesis by simp
qed

lemma rename_variables_pair_pattern: 
  assumes type: "\<And>x. vu_type (R x) = vu_type x"
  shows "rename_variables_pattern R (pair_pattern_untyped p1 p2)
      = pair_pattern_untyped (rename_variables_pattern R p1) (rename_variables_pattern R p2)"
    apply (rule Rep_pattern_untyped_inject[THEN iffD1])
    apply (subst Rep_rename_variables_pattern[OF type])
    apply (subst Rep_pair_pattern_untyped) unfolding Let_def
    apply (subst pu_var_getters_pair_pattern) unfolding Let_def apfst_def map_prod_def
    apply (subst pu_var_getters_rename_variables_pattern[OF type])+
    apply (subst pu_type_rename_variables[OF type])+ 
    apply auto unfolding type by auto

subsection {* Footprints etc. *}

definition "denotation_footprint X d = (\<forall>m m' z. Rep_distr (d m) m' 
    = Rep_distr (d (memory_combine X m z)) (memory_combine X m' z) 
      * (if memory_combine X default m = memory_combine X default m' then 1 else 0))"
lemma denotation_footprint_def': "denotation_footprint X d = (\<forall>m m' z. ennreal_Rep_distr (d m) m' 
    = ennreal_Rep_distr (d (memory_combine X m z)) (memory_combine X m' z) 
      * (if memory_combine X default m = memory_combine X default m' then 1 else 0))"
unfolding ennreal_Rep_distr[symmetric] one_ereal_def zero_ereal_def denotation_footprint_def by auto

definition "program_untyped_footprint X c = denotation_footprint X (denotation_untyped c)"
definition "program_footprint X c = denotation_footprint X (denotation c)"

definition "denotation_readonly X d = (\<forall>m. \<forall>m'\<in>support_distr (d m). \<forall>x\<in>X. Rep_memory m x = Rep_memory m' x)"
definition "program_readonly X c = denotation_readonly X (denotation c)"
definition "program_untyped_readonly X c = denotation_readonly X (denotation_untyped c)"

lemma denotation_readonly_0 [simp]: "denotation_readonly X (\<lambda>m. 0)"
  unfolding denotation_readonly_def
  by (simp add: support_distr_def)


lemma program_readonly_mono:
  assumes mono: "A \<le> B"
  assumes foot: "program_readonly B d"
  shows "program_readonly A d"
by (meson denotation_readonly_def foot mono program_readonly_def subset_iff)



lemma denotation_footprint_mono:
  assumes mono: "A \<ge> B"
  assumes foot: "denotation_footprint B d"
  shows "denotation_footprint A d"
proof (unfold denotation_footprint_def, (rule allI)+)
  fix m m' z
  define dd where "dd == \<lambda>m. Rep_distr (d m)"
(*  have "\<And>m m' z. dd m m' = dd (memory_combine B m z) (memory_combine B m' z) 
      * (if memory_combine B default m = memory_combine B default m' then 1 else 0)"
    using foot unfolding denotation_footprint_def dd_def by simp*)
  define z' where "z' == memory_combine A m z"
  have dd1: "dd m m' = dd (memory_combine B m z') (memory_combine B m' z') 
      * (if memory_combine B default m = memory_combine B default m' then 1 else 0)"
    using foot unfolding denotation_footprint_def dd_def by simp
  have comb1: "memory_combine B m z' = memory_combine A m z"
    unfolding z'_def apply (rule Rep_memory_inject[THEN iffD1])
    unfolding Rep_memory_combine apply (rule ext) using mono by auto
  have comb2: "memory_combine B default m = memory_combine B default m' \<Longrightarrow> memory_combine B m' z' = memory_combine A m' z"
    unfolding z'_def apply (subst (asm) Rep_memory_inject[symmetric])
    apply (subst Rep_memory_inject[symmetric]) 
    unfolding Rep_memory_combine apply (rule ext) using mono apply auto by meson
  have dd2: "dd m m' = dd (memory_combine A m z) (memory_combine A m' z) 
      * (if memory_combine B default m = memory_combine B default m' then 1 else 0)"
    using dd1 comb1 comb2 by auto
  have "dd m m' = dd (memory_combine A m z) (memory_combine A m' z) 
      * (if memory_combine A default m = memory_combine A default m' then 1 else 0)"
  proof (cases "memory_combine A default m = memory_combine A default m'", 
         cases "memory_combine B default m = memory_combine B default m'")
    assume "memory_combine B default m = memory_combine B default m'" and "memory_combine A default m = memory_combine A default m'"
    thus ?thesis using dd2 by auto
  next
    assume Aneq: "memory_combine A default m \<noteq> memory_combine A default m'"
    then obtain x where x: "(if x \<in> A then Rep_memory default x else Rep_memory m x) \<noteq> (if x \<in> A then Rep_memory default x else Rep_memory m' x)"
      apply (subst (asm) Rep_memory_inject[symmetric]) by auto
    hence "x \<notin> A" by auto
    with mono have "x\<notin>B" by auto
    have "memory_combine B default m \<noteq> memory_combine B default m'"
      apply (subst Rep_memory_inject[symmetric], simp)
      apply (subst fun_eq_iff, auto, rule exI[of _ x])
      using `x\<notin>B` `x\<notin>A` x by simp
    with Aneq show ?thesis using dd2 by auto
  next
    assume Aeq: "memory_combine A default m = memory_combine A default m'"
    hence Aeq': "\<And>x. x\<notin>A \<Longrightarrow> Rep_memory m x = Rep_memory m' x"
      apply (subst (asm) Rep_memory_inject[symmetric]) apply auto by metis
    assume Bneq: "memory_combine B default m \<noteq> memory_combine B default m'"
    then obtain  x where x: "(if x \<in> B then Rep_memory default x else Rep_memory m x) \<noteq> (if x \<in> B then Rep_memory default x else Rep_memory m' x)"
      apply (subst (asm) Rep_memory_inject[symmetric]) by auto
    hence "x \<notin> B" by auto
    with x have Bneq': "Rep_memory m x \<noteq> Rep_memory m' x" by auto
    hence "x \<in> A" using Aeq' by auto
    have dd_0: "dd m m' = 0"
      unfolding dd1 using Bneq by simp
    have neq: "memory_combine B default (memory_combine A m z) \<noteq> memory_combine B default (memory_combine A m' z)"
      apply (subst Rep_memory_inject[symmetric], auto)
      apply (drule fun_eq_iff[THEN iffD1]) apply (drule spec[of _ x])
      using `x\<notin>B` `x\<in>A` Bneq' by auto
    have "dd (memory_combine A m z) (memory_combine A m' z) = dd (memory_combine B (memory_combine A m z) xxx) (memory_combine B (memory_combine A m' z) xxx)
        * (if memory_combine B default (memory_combine A m z) = memory_combine B default (memory_combine A m' z) then 1 else 0)"
      using foot unfolding denotation_footprint_def dd_def by auto 
    hence "dd (memory_combine A m z) (memory_combine A m' z) = 0"
      using neq by auto
    with dd_0 show ?thesis by simp
  qed
  thus "Rep_distr (d m) m' =
       Rep_distr (d (memory_combine A m z)) (memory_combine A m' z) *
       (if memory_combine A default m = memory_combine A default m' then 1::real else (0::real))"
    unfolding dd_def by simp
qed


lemma program_untyped_footprint_mono:
  assumes mono: "A \<ge> B"
  assumes foot: "program_untyped_footprint B d"
  shows "program_untyped_footprint A d"
using assms unfolding program_untyped_footprint_def by (rule denotation_footprint_mono)

lemma denotation_footprint_readonly:
  assumes RX: "R\<inter>X={}"
  assumes foot: "denotation_footprint X d"
  shows "denotation_readonly R d"
proof (auto simp: denotation_readonly_def)
  fix m m' x assume "x\<in>R" assume "m' \<in> support_distr (d m)"
  hence "Rep_distr (d m) m' \<noteq> 0" by (simp add: support_distr_def)
  hence "Rep_distr (d (memory_combine X m z)) (memory_combine X m' z) 
      * (if memory_combine X default m = memory_combine X default m' then 1 else 0) \<noteq> 0"
    using assms(2) denotation_footprint_def by auto
  hence "memory_combine X default m = memory_combine X default m'" by (metis (full_types) mult_zero_right)
  thus "Rep_memory m x = Rep_memory m' x"
    by (metis (full_types) Rep_memory_combine `x\<in>R` assms(1) disjoint_iff_not_equal)
qed


lemma program_untyped_footprint_readonly:
  assumes "R\<inter>X={}"
  assumes "program_untyped_footprint X d"
  shows "program_untyped_readonly R d"
using assms denotation_footprint_readonly program_untyped_footprint_def program_untyped_readonly_def by auto

lemma program_footprint_readonly:
  assumes "R\<inter>X={}"
  assumes "program_footprint X d"
  shows "program_readonly R d"
using assms denotation_footprint_readonly program_footprint_def program_readonly_def by auto

lemma denotation_readonly_union:
  assumes "denotation_readonly X c"
  assumes "denotation_readonly Y c"
  shows "denotation_readonly (X\<union>Y) c"
using assms unfolding denotation_readonly_def by blast


lemma program_untyped_readonly_union:
  assumes "program_untyped_readonly X c"
  assumes "program_untyped_readonly Y c"
  shows "program_untyped_readonly (X\<union>Y) c"
using assms unfolding program_untyped_readonly_def
by (rule denotation_readonly_union)



end
