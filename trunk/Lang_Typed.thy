theory Lang_Typed
imports Lang_Untyped
begin

section {* Types *}
  
definition "Type (_::('a::prog_type) itself) 
    = Abs_type \<lparr> tr_domain=range (embedding::'a\<Rightarrow>val),
                 tr_default=embedding (default::'a) \<rparr>";

lemma bool_type: "bool_type = Type TYPE(bool)"
  unfolding bool_type_def Type_def ..

lemma embedding_Type: "embedding (x::'a::prog_type) \<in> t_domain (Type TYPE('a))"
  unfolding Type_def t_domain_def
  by (subst Abs_type_inverse, auto)


section {* Variables *}

datatype ('a::prog_type) variable = Variable variable_name
definition mk_variable_untyped :: "('a::prog_type) variable \<Rightarrow> variable_untyped" where
  "mk_variable_untyped (v::('a::prog_type)variable) = \<lparr> vu_name=(case v of Variable n \<Rightarrow> n), vu_type=Type TYPE('a) \<rparr>"
lemma mk_variable_untyped_type [simp]: "vu_type (mk_variable_untyped (v::'a variable)) = Type TYPE('a::prog_type)"
  unfolding mk_variable_untyped_def by auto
definition var_eq :: "'a::prog_type variable \<Rightarrow> 'b::prog_type variable \<Rightarrow> bool" where
  "var_eq v1 v2 = (mk_variable_untyped v1 = mk_variable_untyped v2)" 
lemma var_eq_same [simp]: "var_eq v v"
  unfolding var_eq_def by simp
lemma var_eq_notsame [simp]: "v\<noteq>w \<Longrightarrow> \<not> var_eq (Variable v) (Variable w)"
  unfolding var_eq_def mk_variable_untyped_def by simp

section {* Memories *}

definition "memory_lookup m (v::'a variable) :: ('a::prog_type) == embedding_inv (memory_lookup_untyped m (mk_variable_untyped v))"
definition "memory_update m (v::'a variable) (a::'a::prog_type) =
  memory_update_untyped m (mk_variable_untyped v) (embedding a)"
lemma memory_lookup_update_same [simp]: "memory_lookup (memory_update m v a) v = a"
  unfolding memory_lookup_def memory_update_def
  by (simp add: memory_lookup_update_same_untyped)
lemma memory_lookup_update_notsame [simp]: 
  "\<not>var_eq v w \<Longrightarrow> memory_lookup (memory_update m v a) w = memory_lookup m w"
  unfolding var_eq_def memory_lookup_def memory_update_def
  by (simp add: memory_lookup_update_notsame_untyped)  
  
section {* Expressions *}

record 'a expression_rep =
  er_fun :: "memory \<Rightarrow> 'a"
  er_vars :: "variable_untyped list"
typedef 'a expression = "{(e::'a expression_rep).
  (\<forall>m1 m2. (\<forall>v\<in>set (er_vars e). Rep_memory m1 v = Rep_memory m2 v) \<longrightarrow> er_fun e m1 = er_fun e m2)}";
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
  by (metis (poly_guards_query) embedding_inv_embedding mk_expression_untyped_fun)

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
  by (smt2 mem_Collect_eq Rep_expression)
definition var_expression :: "('a::prog_type) variable \<Rightarrow> 'a expression" where
"var_expression v = Abs_expression
  \<lparr> er_fun=\<lambda>m. memory_lookup m v,
    er_vars=[mk_variable_untyped v] \<rparr>";
lemma e_fun_var_expression [simp]: "e_fun (var_expression v) = (\<lambda>m. memory_lookup m v)"
  unfolding e_fun_def var_expression_def memory_lookup_def
  by (subst Abs_expression_inverse, auto)

section {* Typed programs *}

definition "assign (v::('a::prog_type) variable) (e::'a expression) =
  Assign (mk_variable_untyped v) (mk_expression_untyped e)"

lemma well_typed_mk_assign [simp]: "well_typed (assign v e)";
  unfolding assign_def by auto  
  
definition "sample (v::('a::prog_type) variable) (e::'a distr expression) =
  Sample (mk_variable_untyped v) (mk_expression_distr e)"

lemma well_typed_mk_sample [simp]: "well_typed (sample v e)";
  unfolding sample_def by simp

(* deprecated \<rightarrow> use parser instead *)  
fun seq :: "program list \<Rightarrow> program" where
  "seq [] = Skip"
| "seq [p] = p"
| "seq (p#pp) = Seq p (seq pp)";


definition ifte :: "bool expression \<Rightarrow> program \<Rightarrow> program \<Rightarrow> program" where
  "ifte e thn els = IfTE (mk_expression_untyped e) thn els"

lemma well_typed_if [simp]: "well_typed thn \<Longrightarrow> well_typed els \<Longrightarrow> well_typed (ifte e thn els)"
  unfolding ifte_def using bool_type by auto 

definition while :: "bool expression \<Rightarrow> program \<Rightarrow> program" where
  "while e p = While (mk_expression_untyped e) p"

lemma well_typed_while [simp]: "well_typed p \<Longrightarrow> well_typed (while e p)"
  unfolding while_def using bool_type by auto

lemma denotation_assign: "denotation (assign v e) m = point_ell1 (memory_update m v (e_fun e m))"
  unfolding assign_def memory_update_def by simp
lemma denotation_sample: "denotation (sample v e) m = apply_to_ell1 (memory_update m v) (distr_to_ell1 (e_fun e m))"
  unfolding sample_def memory_update_def[THEN ext] by auto

lemma denotation_ifte: "denotation (ifte e thn els) m = (if e_fun e m then denotation thn m else denotation els m)"
  by (metis ifte_def denotation.simps(5) e_fun_bool_untyped) 
lemma "denotation (while e p) m = (\<Sum>n. compose_ell1 (\<lambda>m. if e_fun e m then 0 else point_ell1 m)
                                                  (while_iter n (e_fun e) (denotation p) m))"
  unfolding while_def by simp 

section {* Concrete syntax for programs *}

nonterminal program_syntax

syntax "_seq" :: "program_syntax \<Rightarrow> program_syntax \<Rightarrow> program_syntax" (infixr ";" 10)
syntax "_assign" :: "'a variable \<Rightarrow> 'a \<Rightarrow> program_syntax" (infix ":=" 30)
syntax "_sample" :: "'a variable \<Rightarrow> 'a \<Rightarrow> program_syntax" (infix "<-" 30)
syntax "_while" :: "bool \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("while ( _ ) _" [0,20] 20)
syntax "_ifte" :: "bool \<Rightarrow> program_syntax \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("if ( _ ) _ else _" [0,20] 20)
syntax "_ifthen" :: "bool \<Rightarrow> program_syntax \<Rightarrow> program_syntax" ("if ( _ ) _" [0,20] 20)
syntax "" :: "program_syntax \<Rightarrow> program_syntax" ("{ _ }")
syntax "" :: "program_syntax \<Rightarrow> program_syntax" ("{ _ ; }")
syntax "" :: "program_syntax \<Rightarrow> term" ("PROGRAM [ _ ]")
syntax "" :: "program_syntax \<Rightarrow> term" ("PROGRAM [ _ ; ]")

(* This constant should not occur in final terms, it is used in the parsing process *)
consts "MARK_variable" :: "'a variable \<Rightarrow> 'a"
       "MARK_expression" :: "'a \<Rightarrow> 'a expression"
syntax "_access" :: "'a variable \<Rightarrow> 'a" ("$ _" [1000] 999)

(*translations "_assign v e" => "CONST assign v (CONST const_expression e)" *)
translations "_assign v e" => "CONST assign v (CONST MARK_expression e)"
translations "_sample v e" => "CONST sample v (CONST MARK_expression e)"
translations "_while e p" => "CONST Lang_Typed.while (CONST MARK_expression e) p"
translations "_ifte e p1 p2" => "CONST Lang_Typed.ifte (CONST MARK_expression e) p1 p2"
translations "_ifthen e p" => "CONST Lang_Typed.ifte (CONST MARK_expression e) p (CONST Skip)"
translations "_seq p1 p2" => "CONST Seq p1 p2"
translations "_access v" => "CONST MARK_variable v"

(* translate_expression e" takes finds each occurrence of "MARK_variable x"
    and replaces it by a bound variable. Then it applies "const_expression"
    to the result and applies the resulting expression with "apply_expression" to 
    all variables that have been replaced.

    Example: MARK_expression x + MARK_expression y
        \<leadsto> apply_expression (apply_expression (const_expression (\<lambda>x y. x+y)) x) y
*)
ML {*
  fun get_variable_names' l (Const(@{const_syntax MARK_variable},_)$v) = 
        (case v of (Const("_constrain",_) $ Free(vn,_) $ Free(_,_)) => (vn,v)::l
                 | _ => (@{print} v; ("x",v)::l))
    | get_variable_names' l (p$q) = let val l'=get_variable_names' l p in get_variable_names' l' q end
    | get_variable_names' l (Abs(_,_,t)) = get_variable_names' l t
    | get_variable_names' l _ = l
  fun get_variable_names e = rev (get_variable_names' [] e) (* TODO: remove duplicates *)

  fun replace_variable i v (e as Const(@{const_syntax MARK_variable},_)$v') = 
              if v=v' then Bound i else e
    | replace_variable i v (e$f) = replace_variable i v e $ replace_variable i v f
    | replace_variable i v (Abs(n,T,t)) = Abs(n,T,replace_variable (i+1) v t)
    | replace_variable _ _ e = e
  fun abstract_variable (vn,v) e = Abs(vn,dummyT,replace_variable 0 v e)
  fun apply_expression (_,v) e = Const(@{const_name apply_expression},dummyT) $ e $ v
  fun translate_expression (e:term) = 
    let val vars = get_variable_names e
        val rev_vars = rev vars
        val e = fold abstract_variable rev_vars e
        val e = Const(@{const_name const_expression},dummyT) $ e
        val e = fold apply_expression vars e
    in
      e
    end
*}
parse_translation {* [(@{const_syntax MARK_expression}, fn ctx => fn p => translate_expression (hd p))] *}
consts y :: "int variable"
declare [[syntax_ast_trace = false]] term "\<lambda>z. PROGRAM[ x := ($z+$y) ]"


end
