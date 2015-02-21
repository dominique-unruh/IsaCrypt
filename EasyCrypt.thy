theory EasyCrypt
imports EC_Untyped Hoare_Untyped
begin


instantiation unit :: prog_type begin;
instance sorry
end;

instantiation int :: prog_type begin;
instance sorry
end;

instantiation "fun" :: (prog_type,prog_type)prog_type begin;
instance sorry
end;

instantiation "distr" :: (prog_type)prog_type begin
instance sorry
end;

typedef ('a::prog_type) Variable = "{(v::variable). v_type v=Type (TYPE('a))}";
  by (rule exI[of _ "\<lparr>v_name=[],v_type=Type (TYPE('a))\<rparr>"], simp);
definition mk_variable :: "string \<Rightarrow> ('a::prog_type) Variable" where
  "mk_variable v = Abs_Variable \<lparr> v_name = v, v_type=Type TYPE('a) \<rparr>"

record 'a Expression_rep =
  Er_fun :: "memory \<Rightarrow> 'a"
  Er_vars :: "variable list"
typedef 'a Expression = "{(e::'a Expression_rep).
  (\<forall>m1 m2. (\<forall>v\<in>set (Er_vars e). Rep_memory m1 v = Rep_memory m2 v) \<longrightarrow> Er_fun e m1 = Er_fun e m2)}";
  by (rule exI[of _ "\<lparr> Er_fun=(\<lambda>m. undefined),
                       Er_vars=[] \<rparr>"], simp);
definition "E_fun e == Er_fun (Rep_Expression e)"
definition "E_vars e == Er_vars (Rep_Expression e)"
(*typedef ('a::prog_type) ExpressionD = "{(e::'a distr Expression_rep).
  (\<forall>m1 m2. (\<forall>v\<in>set (Er_vars e). Rep_memory m1 v = Rep_memory m2 v) \<longrightarrow> Er_fun e m1 = Er_fun e m2)}";
  by (rule exI[of _ "\<lparr> Er_fun=(\<lambda>m. undefined),
                       Er_vars=[] \<rparr>"], simp);
definition "ED_fun e == Er_fun (Rep_ExpressionD e)"
definition "ED_vars e == Er_vars (Rep_ExpressionD e)"*)

(*
typedef ('a::prog_type) Expression = "{(e::expression). e_type e = Type TYPE('a)}";
  apply (rule exI[of _ "Abs_expression \<lparr> er_fun=(\<lambda>m. t_default (Type TYPE('a))),
                                         er_type=Type TYPE('a),
                                         er_vars=[] \<rparr>"]);
  apply (simp add: e_type_def t_default_def)
  apply (subst Abs_expression_inverse, auto);
  by (metis Rep_type t_domain_def mem_Collect_eq);
*)

definition const_expression :: "'a \<Rightarrow> 'a Expression" where
 "const_expression x = Abs_Expression \<lparr> Er_fun=\<lambda>m. x, Er_vars=[] \<rparr>";
lemma E_fun_const_expression [simp]: "E_fun (const_expression a) m = a"
  unfolding E_fun_def const_expression_def
  by (subst Abs_Expression_inverse, auto)

definition apply_expression :: "('a\<Rightarrow>'b)Expression \<Rightarrow> ('a::prog_type) Variable \<Rightarrow> 'b Expression" where
"apply_expression e v = Abs_Expression
  \<lparr> Er_fun=\<lambda>m. (E_fun e m) (embedding_inv (Rep_memory m (Rep_Variable v))),
    Er_vars=Rep_Variable v#E_vars e \<rparr>";
definition var_expression :: "('a::prog_type) Variable \<Rightarrow> 'a Expression" where
"var_expression v = Abs_Expression
  \<lparr> Er_fun=\<lambda>m. embedding_inv (Rep_memory m (Rep_Variable v)),
    Er_vars=[Rep_Variable v] \<rparr>";

definition "mk_assign (v::('a::prog_type) Variable) (e::'a Expression) =
  Assign (Rep_Variable v) 
  (Abs_expression \<lparr> er_fun=\<lambda>m. embedding (E_fun e m),
                    er_type=Type TYPE('a),
                    er_vars=E_vars e \<rparr>)"

lemma well_typed_mk_assign [simp]: "well_typed (mk_assign v e)";
  apply (subst mk_assign_def, auto)
  unfolding e_type_def
  apply (subst Abs_expression_inverse, auto)
  apply (subst Type_def)
  unfolding t_domain_def
  apply (subst Abs_type_inverse, auto)
  apply (smt2 E_fun_def E_vars_def Rep_Expression mem_Collect_eq)
  by (metis (full_types) Rep_Variable mem_Collect_eq)
  
definition "mk_sample (v::('a::prog_type) Variable) (e::'a distr Expression) =
  Sample (Rep_Variable v) 
  (Abs_expressiond \<lparr> edr_fun=\<lambda>m. apply_to_distr embedding (E_fun e m),
                     edr_type=Type TYPE('a),
                     edr_vars=E_vars e \<rparr>)"

lemma well_typed_mk_sample [simp]: "well_typed (mk_sample v e)";
  sorry  
  

fun mk_seq :: "program list \<Rightarrow> program" where
  "mk_seq [] = Skip"
| "mk_seq [p] = p"
| "mk_seq (p#pp) = Seq p (mk_seq pp)";

definition mk_if :: "bool Expression \<Rightarrow> program \<Rightarrow> program \<Rightarrow> program" where
  "mk_if e thn els = IfTE (Abs_expression
    \<lparr> er_fun=\<lambda>m. embedding (E_fun e m),
      er_type=Type TYPE(bool),
      er_vars=E_vars e \<rparr>) thn els"

lemma well_typed_if [simp]: "well_typed thn \<Longrightarrow> well_typed els \<Longrightarrow> well_typed (mk_if e thn els)"
  sorry

definition mk_while :: "bool Expression \<Rightarrow> program \<Rightarrow> program" where
  "mk_while e p = While (Abs_expression
    \<lparr> er_fun=\<lambda>m. embedding (E_fun e m),
      er_type=Type TYPE(bool),
      er_vars=E_vars e \<rparr>) p"

lemma well_typed_while [simp]: "well_typed p \<Longrightarrow> well_typed (mk_while e p)"
  sorry
  
definition "memory_lookup m (v::'a Variable) :: ('a::prog_type) == embedding_inv (Rep_memory m (Rep_Variable v))"
definition "memory_Update m (v::'a Variable) (a::'a::prog_type) =
  memory_update m (Rep_Variable v) (embedding a)"
lemma memory_lookup_Update [simp]: "memory_lookup (memory_Update m v a) v = a"
  sorry  

end
