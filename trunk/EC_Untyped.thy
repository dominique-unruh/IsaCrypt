theory EC_Untyped
imports Main Setsum_Infinite Real_Vector_Spaces Series Orderings
begin




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
(* TODO: These should be compatible with "Type TYPE(bool)" ! *)
(*axiomatization
   bool_true :: val and bool_false :: val
where
   bool_true_false: "bool_true \<noteq> bool_false";

definition "bool_type = Abs_type \<lparr> tr_domain={bool_true,bool_false}, tr_default=bool_false \<rparr>"*)
record variable = 
  v_name::string
  v_type::type;

(*datatype typeID = TConstrID string "typeID list"*)

class prog_type =
  default +
  fixes embedding :: "'a \<Rightarrow> val"
  fixes embedding_inv :: "val \<Rightarrow> 'a"
(*  fixes type_id :: "'a itself \<Rightarrow> typeID"*)
  assumes inj_embedding [simp]: "embedding_inv (embedding x) = x"
  assumes val_closed [simp]: "closed_val_set (range embedding)";

instantiation "bool" :: prog_type begin
instance sorry
end
definition "Type (_::('a::prog_type) itself) 
    = Abs_type \<lparr> tr_domain=range (embedding::'a\<Rightarrow>val),
                 tr_default=embedding (default::'a) \<rparr>";


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


typedef 'a distr = "{\<mu>::'a\<Rightarrow>real. (\<forall>x. \<mu> x\<ge>0) \<and> (\<exists>b\<le>1. SetSums_to \<mu> UNIV b)}"
  apply (rule exI[where x="\<lambda>x. 0"], auto) unfolding SetSums_def
  apply (rule exI[where x=0])
  using setsum_0 by auto
definition support :: "'a distr \<Rightarrow> 'a set" where
  "support \<mu> = {x. Rep_distr \<mu> x > 0}"
instantiation distr :: (type) zero begin
definition zero_distr :: "'a distr" where "zero_distr = Abs_distr (\<lambda>x. 0)";
instance ..
end
definition point_distr :: "'a \<Rightarrow> 'a distr" where "point_distr a = Abs_distr (\<lambda>x. if x=a then 1 else 0)";
consts compose_distr :: "('a \<Rightarrow> 'b distr) \<Rightarrow> 'a distr \<Rightarrow> 'b distr";
definition apply_to_distr :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a distr \<Rightarrow> 'b distr" where
  "apply_to_distr f = compose_distr (\<lambda>x. point_distr (f x))"

record expressiond_rep =
  edr_fun :: "memory \<Rightarrow> val distr"
  edr_type :: type
  edr_vars :: "variable list"
typedef expressiond = "{(e::expressiond_rep).
  (\<forall>m. support (edr_fun e m) \<subseteq> t_domain (edr_type e)) \<and>
  (\<forall>m1 m2. (\<forall>v\<in>set (edr_vars e). Rep_memory m1 v = Rep_memory m2 v) \<longrightarrow> edr_fun e m1 = edr_fun e m2)}";
  apply (rule exI[of _ "\<lparr> edr_fun=\<lambda>m. 0,
                          edr_type=undefined,
                          edr_vars=[] \<rparr>"], simp);
  unfolding support_def zero_distr_def
  apply (subst Abs_distr_inverse, auto)
  apply (rule exI[where x=0], auto)
  by (rule setsum_0)
definition "ed_fun e == edr_fun (Rep_expressiond e)"
definition "ed_type e == edr_type (Rep_expressiond e)"
definition "ed_vars e == edr_vars (Rep_expressiond e)"


datatype program =
  Assign variable expression
| Sample variable expressiond
| Seq program program
| Skip
| IfTE expression program program
| While expression program


fun well_typed :: "program \<Rightarrow> bool" where
  "well_typed (Seq p1 p2) = (well_typed p1 \<and> well_typed p2)"
| "well_typed (Assign v e) = (e_type e = v_type v)"
| "well_typed (Sample v e) = (ed_type e = v_type v)"
| "well_typed Skip = True"
| "well_typed (While e p) = ((e_type e = Type TYPE(bool)) \<and> well_typed p)"
| "well_typed (IfTE e thn els) = ((e_type e = Type TYPE(bool)) \<and> well_typed thn \<and> well_typed els)";

typedef 'a ell1 = "{\<mu>::'a\<Rightarrow>real. SetSums (\<lambda>x. abs(\<mu> x)) UNIV}"
  apply (rule exI[of _ "\<lambda>x. 0"], auto) unfolding SetSums_def
  using setsum_0 by auto

instantiation ell1 :: (type) zero begin
definition zero_ell1 :: "'a ell1" where "zero_ell1 = Abs_ell1 (\<lambda>x. 0)";
instance ..
end

instantiation ell1 :: (type) comm_monoid_add begin
definition "\<mu> + \<nu> = Abs_ell1 (\<lambda>x. Rep_ell1 \<mu> x + Rep_ell1 \<nu> x)"
instance apply intro_classes sorry
end

instantiation ell1 :: (type) real_vector begin
definition "\<mu> - \<nu> = Abs_ell1 (\<lambda>x. Rep_ell1 \<mu> x - Rep_ell1 \<nu> x)"
definition "-(\<nu>::'a ell1) = 0-\<nu>"
definition "scaleR r (\<mu>::'a ell1) = Abs_ell1 (\<lambda>x. r * Rep_ell1 \<mu> x)" 
instance apply intro_classes sorry
end

instantiation ell1 :: (type) real_normed_vector begin
definition "norm_ell1 (s::'a ell1) = SetSum (\<lambda>x. abs(Rep_ell1 s x)) UNIV"
definition "dist_ell1 (s::'a ell1) t = norm (s-t)"
definition "open_ell1 (S::'a ell1 set) = (\<forall>x\<in>S. \<exists>e>0. \<forall>y. dist y x < e \<longrightarrow> y \<in> S)"
definition "sgn_ell1 (s::'a ell1) = s /\<^sub>R norm s"
instance apply intro_classes sorry
end

instantiation ell1 :: (type) order begin
definition "s \<le> (t::'a ell1) = (\<forall>x. Rep_ell1 s x \<le> Rep_ell1 t x)"
definition "s < (t::'a ell1) = (s \<le> t \<and> s \<noteq> t)"
instance apply intro_classes sorry
end

instantiation ell1 :: (type) ordered_real_vector begin
instance apply intro_classes sorry
end


definition point_ell1 :: "'a \<Rightarrow> 'a ell1" where "point_ell1 a = Abs_ell1 (\<lambda>x. if x=a then 1 else 0)";
consts compose_ell1 :: "('a \<Rightarrow> 'b ell1) \<Rightarrow> 'a ell1 \<Rightarrow> 'b ell1";
definition apply_to_ell1 :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a ell1 \<Rightarrow> 'b ell1" where
  "apply_to_ell1 f = compose_ell1 (\<lambda>x. point_ell1 (f x))"
definition "distr_to_ell1 \<mu> = Abs_ell1 (Rep_distr \<mu>)"
definition "support_ell1 \<mu> = {x. Rep_ell1 \<mu> x \<noteq> 0}"

type_synonym denotation = "memory \<Rightarrow> memory ell1"

fun while_iter :: "nat \<Rightarrow> expression \<Rightarrow> denotation \<Rightarrow> memory \<Rightarrow> memory ell1" where
  "while_iter 0 e p m = point_ell1 m"
| "while_iter (Suc n) e p m = compose_ell1 (\<lambda>m. if e_fun e m = embedding True then p m else 0)
                                            (while_iter n e p m)"

fun denotation :: "program \<Rightarrow> denotation" where
  "denotation (Seq p1 p2) m = compose_ell1 (denotation p2) (denotation p1 m)"
| "denotation (Assign v e) m = point_ell1 (memory_update m v (e_fun e m))"
| "denotation (Sample v e) m = apply_to_ell1 (memory_update m v) (distr_to_ell1 (ed_fun e m))"
| "denotation (Skip) m = point_ell1 m"
| "denotation (IfTE e thn els) m = (if (e_fun e m = embedding True) then denotation thn m else denotation els m)"
| "denotation (While e p) m = (\<Sum>n. compose_ell1 (\<lambda>m. if e_fun e m = embedding True then 0 else point_ell1 m)
                                                  (while_iter n e (denotation p) m))"

fun vars :: "program \<Rightarrow> variable list" where
  "vars Skip = []"
| "vars (Seq p1 p2) = (vars p1) @ (vars p2)"
| "vars (Assign v e) = v # e_vars e"
| "vars (Sample v e) = v # ed_vars e"
| "vars (IfTE e p1 p2) = e_vars e @ vars p1 @ vars p2"
| "vars (While e p) = e_vars e @ vars p"

definition uniform :: "'a set \<Rightarrow> 'a distr" where
  "uniform S = Abs_distr (\<lambda>x. if x \<in> S then 1/(card S) else 0)"

end;
