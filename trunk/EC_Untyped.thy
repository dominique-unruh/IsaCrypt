theory EC_Untyped
imports Main
begin

(*
definition SetSum :: "('a \<Rightarrow> 'b::{t2_space}) \<Rightarrow> ('a set) \<Rightarrow> 'b" where
  "SetSum f A = Lim () (setsum f)
*)

typedecl val;
(*coinductive closed_val_set :: "val set \<Rightarrow> bool" where
  "closed_val_set x \<Longrightarrow> y \<subseteq> x \<Longrightarrow> closed_val_set y"
| "closed_val_set x \<Longrightarrow> closed_val_set y \<Longrightarrow>
   (\<exists>z f. closed_val_set z \<and> *)
axiomatization closed_val_set :: "val set \<Rightarrow> bool" where
  closed_val_set_undefined: "closed_val_set {undefined}";

(* Should contain a set of values. Additionally, there should be conversion tools to/from Isabelle types *)
record type_rep = 
  tr_domain :: "val set"
  tr_default :: "val"
typedef type = "{(t::type_rep). tr_default t \<in> tr_domain t \<and> closed_val_set (tr_domain t)}";
  by (metis (no_types, lifting) closed_val_set_undefined mem_Collect_eq select_convs(1) select_convs(2) singletonI)
(*  apply (rule exI[of _ "\<lparr> tr_domain={undefined}, tr_default=undefined \<rparr>"]);
  by (auto simp: closed_val_set_undefined); *)
definition t_domain :: "type \<Rightarrow> val set" where
  "t_domain t = tr_domain (Rep_type t)";
definition t_default :: "type \<Rightarrow> val" where
  "t_default t = tr_default (Rep_type t)";

record variable = 
  v_name::string
  v_type::type;


typedef memory = "{(m::variable\<Rightarrow>val). (\<forall>v. m v \<in> t_domain (v_type v))}"
  apply (rule exI[of _ "\<lambda>v. t_default (v_type v)"], simp);
  by (metis Rep_type mem_Collect_eq t_default_def t_domain_def)

definition "memory_update m v x = Abs_memory ((Rep_memory m)(v:=if x\<in>t_domain(v_type v) then x else t_default(v_type v)))";

record expression_rep =
  er_fun :: "memory \<Rightarrow> val"
  er_type :: type
  er_vars :: "variable list"
typedef expression = "{(e::expression_rep).
  (\<forall>m. er_fun e m \<in> t_domain (er_type e)) \<and>
  (\<forall>m1 m2. (\<forall>v\<in>set (er_vars e). Rep_memory m1 v = Rep_memory m2 v) \<longrightarrow> er_fun e m1 = er_fun e m2)}";
  apply (rule exI[of _ "\<lparr> er_fun=(\<lambda>m. t_default undefined),
                          er_type=undefined,
                          er_vars=[] \<rparr>"], simp);
  by (metis Rep_type mem_Collect_eq t_default_def t_domain_def);
definition "e_fun e == er_fun (Rep_expression e)"
definition "e_type e == er_type (Rep_expression e)"
definition "e_vars e == er_vars (Rep_expression e)"

datatype program =
  Assign "variable" expression
| Seq program program

fun well_typed :: "program \<Rightarrow> bool" where
  "well_typed (Seq p1 p2) = (well_typed p1 \<and> well_typed p2)"
| "well_typed (Assign v e) = (e_type e = v_type v)";

typedecl 'a distr;
consts point_distr :: "'a \<Rightarrow> 'a distr";
consts compose_distr :: "('a \<Rightarrow> 'b distr) \<Rightarrow> 'a distr \<Rightarrow> 'b distr";
consts in_supp :: "'a \<Rightarrow> 'a distr \<Rightarrow> bool";

fun denotation :: "program \<Rightarrow> (memory \<Rightarrow> memory distr)" where
  "denotation (Seq p1 p2) m = compose_distr (denotation p2) (denotation p1 m)"
| "denotation (Assign v e) m = point_distr (memory_update m v (e_fun e m))";

definition "hoare pre prog post =
  (\<forall>m. pre m \<longrightarrow> (\<forall>m'. in_supp m' (denotation prog m) \<longrightarrow> post m))";

end;
