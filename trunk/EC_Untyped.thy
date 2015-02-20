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
axiomatization
   bool_true :: val and bool_false :: val
where
   bool_true_false: "bool_true \<noteq> bool_false";

definition "bool_type = Abs_type \<lparr> tr_domain={bool_true,bool_false}, tr_default=bool_false \<rparr>"
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
| Skip
| IfTE expression program program
| While expression program

fun well_typed :: "program \<Rightarrow> bool" where
  "well_typed (Seq p1 p2) = (well_typed p1 \<and> well_typed p2)"
| "well_typed (Assign v e) = (e_type e = v_type v)"
| "well_typed Skip = True"
| "well_typed (While e p) = ((e_type e = bool_type) \<and> well_typed p)"
| "well_typed (IfTE e thn els) = ((e_type e = bool_type) \<and> well_typed thn \<and> well_typed els)";

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
consts in_supp :: "'a \<Rightarrow> 'a ell1 \<Rightarrow> bool";

type_synonym denotation = "memory \<Rightarrow> memory ell1"

fun while_iter :: "nat \<Rightarrow> expression \<Rightarrow> denotation \<Rightarrow> memory \<Rightarrow> memory ell1" where
  "while_iter 0 e p m = point_ell1 m"
| "while_iter (Suc n) e p m = compose_ell1 (\<lambda>m. if e_fun e m = bool_true then p m else 0)
                                            (while_iter n e p m)"

fun denotation :: "program \<Rightarrow> denotation" where
  "denotation (Seq p1 p2) m = compose_ell1 (denotation p2) (denotation p1 m)"
| "denotation (Assign v e) m = point_ell1 (memory_update m v (e_fun e m))"
| "denotation (Skip) m = point_ell1 m"
| "denotation (IfTE e thn els) m = (if (e_fun e m = bool_true) then denotation thn m else denotation els m)"
| "denotation (While e p) m = (\<Sum>n. compose_ell1 (\<lambda>m. if e_fun e m = bool_true then 0 else point_ell1 m)
                                                  (while_iter n e (denotation p) m))"


fun vars :: "program \<Rightarrow> variable list" where
  "vars Skip = []"
| "vars (Seq p1 p2) = (vars p1) @ (vars p2)"
| "vars (Assign v e) = v # e_vars e"
| "vars (IfTE e p1 p2) = e_vars e @ vars p1 @ vars p2"
| "vars (While e p) = e_vars e @ vars p"

definition "hoare pre prog post =
  (\<forall>m. pre m \<longrightarrow> (\<forall>m'. in_supp m' (denotation prog m) \<longrightarrow> post m))";

end;
