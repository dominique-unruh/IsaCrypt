theory EasyCrypt
imports EC_Untyped
begin
  
class prog_type =
  default +
  fixes embedding :: "'a \<Rightarrow> val"
  fixes embedding_inv :: "val \<Rightarrow> 'a"
  assumes inj_embedding: "embedding_inv (embedding x) = y"
  assumes val_closed : "closed_val_set (range embedding)";

instantiation unit :: prog_type begin;
instance sorry
end;

instantiation int :: prog_type begin;
instance sorry
end;

instantiation "fun" :: (prog_type,prog_type)prog_type begin;
instance sorry
end;

instantiation "bool" :: prog_type begin
definition "default_bool = bool_false"
definition "embedding_bool b = (if b then bool_true else bool_false)"
definition "embedding_inv_bool v = (if v=bool_true then True else False)"
instance sorry
end

definition "Type (_::('a::prog_type) itself) 
    = Abs_type \<lparr> tr_domain=range (embedding::'a\<Rightarrow>val),
                 tr_default=embedding (default::'a) \<rparr>";

typedef ('a::prog_type) Variable = "{(v::variable). v_type v=Type (TYPE('a))}";
  by (rule exI[of _ "\<lparr>v_name=[],v_type=Type (TYPE('a))\<rparr>"], simp);
definition mk_variable :: "string \<Rightarrow> ('a::prog_type) Variable" where
  "mk_variable v = Abs_Variable \<lparr> v_name = v, v_type=Type TYPE('a) \<rparr>"

typedef ('a::prog_type) Expression = "{(e::expression). e_type e = Type TYPE('a)}";
  apply (rule exI[of _ "Abs_expression \<lparr> er_fun=(\<lambda>m. t_default (Type TYPE('a))),
                                         er_type=Type TYPE('a),
                                         er_vars=[] \<rparr>"]);
  apply (simp add: e_type_def t_default_def)
  apply (subst Abs_expression_inverse, auto);
  by (metis Rep_type t_domain_def mem_Collect_eq);

definition const_expression :: "'a::prog_type \<Rightarrow> 'a Expression" where
 "const_expression x = Abs_Expression (Abs_expression
  \<lparr> er_fun=\<lambda>m. embedding x,
    er_type=Type TYPE('a),
    er_vars=[] \<rparr>)";
definition apply_expression :: "('a\<Rightarrow>'b::prog_type)Expression \<Rightarrow> ('a::prog_type) Variable \<Rightarrow> 'b Expression" where
"apply_expression e v = Abs_Expression (Abs_expression
  \<lparr> er_fun=\<lambda>m. embedding ((embedding_inv::val\<Rightarrow>'a\<Rightarrow>'b)(e_fun(Rep_Expression e) m)
                         (embedding_inv(Rep_memory m (Rep_Variable v)))),
    er_type=Type TYPE('b),
    er_vars=Rep_Variable v#e_vars(Rep_Expression e) \<rparr>)";

definition "mk_assign (v::('a::prog_type) Variable) (e::'a Expression) =
  Assign (Rep_Variable v) (Rep_Expression e)";

lemma well_typed_mk_assign [simp]: "well_typed (mk_assign v e)";
by (metis (mono_tags, lifting) mk_assign_def Rep_Expression Rep_Variable mem_Collect_eq well_typed.simps(2))

fun mk_seq :: "program list \<Rightarrow> program" where
  "mk_seq [] = Skip"
| "mk_seq [p] = p"
| "mk_seq (p#pp) = Seq p (mk_seq pp)";

definition mk_if :: "bool Expression \<Rightarrow> program \<Rightarrow> program \<Rightarrow> program" where
  "mk_if e thn els = IfTE (Rep_Expression e) thn els"

lemma well_typed_if [simp]: "well_typed thn \<Longrightarrow> well_typed els \<Longrightarrow> well_typed (mk_if e thn els)"
proof -
  fix thn els assume "well_typed thn" and "well_typed els"
  have "e_type (Rep_Expression e) = Type TYPE(bool)" using Rep_Expression ..
  have "Type TYPE(bool) = bool_type"
    unfolding Type_def bool_type_def 
    unfolding default_bool_def embedding_bool_def[THEN ext]
    apply auto
    using default_bool_def

  show "well_typed (mk_if e thn els)"
    unfolding mk_if_def apply simp
    
  unfolding mk_if_def
using Rep_Expression
  apply (auto simp: Rep_Expression)

  

definition "(x::int Variable) = mk_variable ''x''"
definition "(y::int Variable) = mk_variable ''y''"

definition "example = mk_seq 
  [mk_assign x (const_expression 0),
   mk_assign y (apply_expression (apply_expression (const_expression (\<lambda>x y. x+y)) x) y)]"
lemma well_typed_example: "well_typed example"
  unfolding example_def by simp

end
