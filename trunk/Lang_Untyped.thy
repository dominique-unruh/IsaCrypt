theory Lang_Untyped
imports Main Setsum_Infinite Orderings Series Ell1 Universe
begin


record type_rep = 
  tr_domain :: "val set"
  tr_default :: "val"
typedef type = "{(t::type_rep). tr_default t \<in> tr_domain t \<and> closed_val_set (tr_domain t)}";
  by (metis (no_types, lifting) closed_val_set_undefined mem_Collect_eq select_convs(1) select_convs(2) singletonI)
definition t_domain :: "type \<Rightarrow> val set" where
  "t_domain t = tr_domain (Rep_type t)";
definition t_default :: "type \<Rightarrow> val" where
  "t_default t = tr_default (Rep_type t)";
type_synonym variable_name = string
record variable_untyped = 
  vu_name::variable_name
  vu_type::type;

definition "bool_type =
      Abs_type \<lparr> tr_domain=range (embedding::bool\<Rightarrow>val),
                 tr_default=embedding (default::bool) \<rparr>"



typedef memory = "{(m::variable_untyped\<Rightarrow>val). (\<forall>v. m v \<in> t_domain (vu_type v))}"
  apply (rule exI[of _ "\<lambda>v. t_default (vu_type v)"], simp);
  by (metis Rep_type mem_Collect_eq t_default_def t_domain_def)

abbreviation "memory_lookup_untyped == Rep_memory"
definition "memory_update_untyped m v x = 
  Abs_memory ((Rep_memory m)(v:=if x\<in>t_domain(vu_type v) then x else t_default(vu_type v)))";
lemma memory_lookup_update_same_untyped: "memory_lookup_untyped (memory_update_untyped m v a) v = a"
  sorry
lemma memory_lookup_update_notsame_untyped: 
  "v \<noteq> w \<Longrightarrow> memory_lookup_untyped (memory_update_untyped m v a) w = memory_lookup_untyped m w"
  sorry

record expression_untyped_rep =
  eur_fun :: "memory \<Rightarrow> val"
  eur_type :: type
  eur_vars :: "variable_untyped list"
typedef expression_untyped = "{(e::expression_untyped_rep).
  (\<forall>m. eur_fun e m \<in> t_domain (eur_type e)) \<and>
  (\<forall>m1 m2. (\<forall>v\<in>set (eur_vars e). Rep_memory m1 v = Rep_memory m2 v) \<longrightarrow> eur_fun e m1 = eur_fun e m2)}";
  apply (rule exI[of _ "\<lparr> eur_fun=(\<lambda>m. t_default undefined),
                          eur_type=undefined,
                          eur_vars=[] \<rparr>"], simp);
  by (metis Rep_type mem_Collect_eq t_default_def t_domain_def);
definition "eu_fun e == eur_fun (Rep_expression_untyped e)"
definition "eu_type e == eur_type (Rep_expression_untyped e)"
definition "eu_vars e == eur_vars (Rep_expression_untyped e)"



record expression_distr_rep =
  edr_fun :: "memory \<Rightarrow> val distr"
  edr_type :: type
  edr_vars :: "variable_untyped list"
typedef expression_distr = "{(e::expression_distr_rep).
  (\<forall>m. support_distr (edr_fun e m) \<subseteq> t_domain (edr_type e)) \<and>
  (\<forall>m1 m2. (\<forall>v\<in>set (edr_vars e). Rep_memory m1 v = Rep_memory m2 v) \<longrightarrow> edr_fun e m1 = edr_fun e m2)}";
  apply (rule exI[of _ "\<lparr> edr_fun=\<lambda>m. 0,
                          edr_type=undefined,
                          edr_vars=[] \<rparr>"], simp);
  unfolding support_distr_def zero_distr_def
  apply (subst Abs_distr_inverse, auto)
  apply (rule exI[where x=0], auto)
  by (rule setsum_0)
definition "ed_fun e == edr_fun (Rep_expression_distr e)"
definition "ed_type e == edr_type (Rep_expression_distr e)"
definition "ed_vars e == edr_vars (Rep_expression_distr e)"


datatype program =
  Assign variable_untyped expression_untyped
| Sample variable_untyped expression_distr
| Seq program program
| Skip
| IfTE expression_untyped program program
| While expression_untyped program


fun well_typed :: "program \<Rightarrow> bool" where
  "well_typed (Seq p1 p2) = (well_typed p1 \<and> well_typed p2)"
| "well_typed (Assign v e) = (eu_type e = vu_type v)"
| "well_typed (Sample v e) = (ed_type e = vu_type v)"
| "well_typed Skip = True"
| "well_typed (While e p) = ((eu_type e = bool_type) \<and> well_typed p)"
| "well_typed (IfTE e thn els) = ((eu_type e = bool_type) \<and> well_typed thn \<and> well_typed els)";

type_synonym denotation = "memory \<Rightarrow> memory ell1"

fun while_iter :: "nat \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> denotation \<Rightarrow> memory \<Rightarrow> memory ell1" where
  "while_iter 0 e p m = point_ell1 m"
| "while_iter (Suc n) e p m = 
      compose_ell1 (\<lambda>m. if e m then p m else 0)
                    (while_iter n e p m)"

fun denotation :: "program \<Rightarrow> denotation" where
  "denotation (Seq p1 p2) m = compose_ell1 (denotation p2) (denotation p1 m)"
| "denotation (Assign v e) m = point_ell1 (memory_update_untyped m v (eu_fun e m))"
| "denotation (Sample v e) m = apply_to_ell1 (memory_update_untyped m v) (distr_to_ell1 (ed_fun e m))"
| "denotation (Skip) m = point_ell1 m"
| "denotation (IfTE e thn els) m = (if (eu_fun e m = embedding True) then denotation thn m else denotation els m)"
| "denotation (While e p) m = (\<Sum>n. compose_ell1 (\<lambda>m. if eu_fun e m = embedding True then 0 else point_ell1 m)
                                                  (while_iter n (\<lambda>m. eu_fun e m = embedding True) (denotation p) m))"

fun vars :: "program \<Rightarrow> variable_untyped list" where
  "vars Skip = []"
| "vars (Seq p1 p2) = (vars p1) @ (vars p2)"
| "vars (Assign v e) = v # eu_vars e"
| "vars (Sample v e) = v # ed_vars e"
| "vars (IfTE e p1 p2) = eu_vars e @ vars p1 @ vars p2"
| "vars (While e p) = eu_vars e @ vars p"

end;
