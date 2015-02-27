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

section {* Procedures *}

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

section {* Typed programs *}

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

lemma denotation_seq: "denotation (seq p q) m = 
  compose_distr (denotation_untyped (mk_program_untyped q)) (denotation_untyped (mk_program_untyped p) m)"
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

lemmas denotation_simp = denotation_seq denotation_skip denotation_assign denotation_sample denotation_ifte denotation_while denotation_callproc

section {* Concrete syntax for programs *}

subsection {* Grammar *}

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

subsection {* Translation functions *}

ML {*
  fun is_program_variable ctx (v:string list) (c:string) = 
        if member (op=) v c then true
        else
          (case Proof_Context.read_const {proper = true, strict = false} ctx c of
             Const(_,Type(@{type_name variable},_)) => true
           | _ => false)
          handle ERROR _ => false

  local
  (* known = known variables names *)
  fun get_variable_names' _ _ l (Const("_var_access",_)$v) = 
        (case v of (Const("_constrain",_) $ (v' as Free(vn,_)) $ _) => (vn,v')::l
                 | (Const("_constrain",_) $ v' $ _) => ("var",v')::l
                 | v' => ("var",v')::l)
    | get_variable_names' ctx known l (v as Free(vn,_)) = if is_program_variable ctx (!known) vn then (vn,v)::l else l
    | get_variable_names' ctx known l (Const("_constrain",_)$p$_) = get_variable_names' ctx known l p
    | get_variable_names' ctx known l (p$q) = let val l'=get_variable_names' ctx known l p in get_variable_names' ctx known l' q end
    | get_variable_names' ctx known l (Abs(_,_,t)) = get_variable_names' ctx known l t
    | get_variable_names' _ _ l _ = l
  fun get_variable_names ctx known e = distinct (op=) (get_variable_names' ctx known [] e)

  fun replace_variable i v e =
    if e=v then Bound i else case e of
      (Const("_var_access",_) $ e) => replace_variable i v e
    | e$f => replace_variable i v e $ replace_variable i v f
    | Abs(n,T,t) => Abs(n,T,replace_variable (i+1) v t)
    | e => e

  fun abstract_variable (vn,v) e = Abs(vn,dummyT,replace_variable 0 v e)
  fun apply_expression (_,v) e = Const(@{const_name apply_expression},dummyT) $ e $ v

  fun translate_expression ctx known (e:term) = 
    let val vars = get_variable_names ctx known e
        val rev_vars = rev vars
        val e = fold abstract_variable rev_vars e
        val e = Const(@{const_name const_expression},dummyT) $ e
        val e = fold apply_expression vars e
    in e end

  fun add_var known (Free(v,_)) = (if not (member (op=) (!known) v) then known := v :: !known else ())
    | add_var known (Const("_constrain",_)$p$_) = add_var known p
    | add_var _ _ = ()

  in

  fun translate_program (ctx:Proof.context) known (p:term) =
    let fun trans (Const("_assign",_) $ x $ e) =
                (add_var known x;
                 Const(@{const_syntax assign},dummyT) $ x $ translate_expression ctx known e)
          | trans (Const("_assign_quote",_) $ x $ e) =
                (add_var known x;
                 Const(@{const_syntax assign},dummyT) $ x $ e)
          | trans (Const("_sample",_) $ x $ e) =
                (add_var known x;
                 Const(@{const_syntax sample},dummyT) $ x $ translate_expression ctx known e)
          | trans (Const("_sample_quote",_) $ x $ e) =
                (add_var known x;
                 Const(@{const_syntax sample},dummyT) $ x $ e)
          | trans (Const("_label",_) $ Free(l,_) $ p) = 
                Const(@{const_syntax label},dummyT) $ HOLogic.mk_string l $ trans p
          | trans (Const("_label",_) $ (Const("_constrain",_)$Free(l,_)$_) $ p) = 
                Const(@{const_syntax label},dummyT) $ HOLogic.mk_string l $ trans p
          | trans (Const("_label",_) $ l $ _) = raise (ERROR ("Label must be just an identifier, not "^(@{make_string} l)))
          | trans (Const("_quote",_) $ p) = p
          | trans (Const("_while",_) $ e $ p) =
                 Const(@{const_syntax while},dummyT) $ (translate_expression ctx known e) $ trans p
          | trans (Const("_while_quote",_) $ e $ p) =
                 Const(@{const_syntax while},dummyT) $ e $ trans p
          | trans (Const("_ifthen",_) $ e $ p) =
                 Const(@{const_syntax ifte},dummyT) $ (translate_expression ctx known e) $ trans p $ Const(@{const_syntax skip},dummyT) 
          | trans (Const("_ifte",_) $ e $ p $ q) =
                 Const(@{const_syntax ifte},dummyT) $ (translate_expression ctx known e) $ trans p $ trans q
          | trans (Const("_ifthen_quote",_) $ e $ p) =
                 Const(@{const_syntax ifte},dummyT) $ e $ trans p $ Const(@{const_syntax skip},dummyT) 
          | trans (Const("_ifte_quote",_) $ e $ p $ q) =
                 Const(@{const_syntax ifte},dummyT) $ e $ trans p $ trans q
          | trans (Const("_seq",_) $ p1 $ p2) =
                Const(@{const_syntax seq},dummyT) $ trans p1 $ trans p2
          | trans (Const("_skip",_)) = Const(@{const_syntax skip},dummyT)
          | trans p = raise ERROR ("Invalid program fragment "^(@{make_string} p))
    in trans p end
  end *}

parse_translation {* [("_program", fn ctx => fn p => 
    Const(@{const_syntax program},dummyT) $ 
      translate_program ctx (Unsynchronized.ref[]) (hd p))] *};

ML {*
local
fun dest_nibble t =
  let fun err () = raise TERM ("dest_nibble", [t]) in
    (case try (unprefix "\<^const>String.nibble.Nibble" o fst o Term.dest_Const) t of
      NONE => err ()
    | SOME c =>
        if size c <> 1 then err ()
        else if "0" <= c andalso c <= "9" then ord c - ord "0"
        else if "A" <= c andalso c <= "F" then ord c - ord "A" + 10
        else err ())
  end;

fun dest_char (Const (@{const_syntax String.char.Char}, _) $ t $ u) =
       dest_nibble t * 16 + dest_nibble u
     | dest_char t = raise TERM ("dest_char", [t]);

fun dest_list (Const(@{const_syntax List.list.Nil}, _)) = []
  | dest_list (Const(@{const_syntax List.list.Cons}, _) $ t $ u) = t :: dest_list u
  | dest_list t = raise TERM ("dest_list", [t]);

val dest_string = implode o map (chr o dest_char) o dest_list;


    fun translate_expression_back (Const(@{const_syntax const_expression},_) $ e) = e
      | translate_expression_back (Const(@{const_syntax apply_expression},_) $ e $ x) =
            Term.betapply (translate_expression_back e, Const("_var_access",dummyT) $ x)
      | translate_expression_back _ = (raise (ERROR ("translate_expression_back: error")))
  in
  fun translate_program_back _ p = 
    let fun trans (Const(@{const_syntax skip},_)) = Const("_skip",dummyT)
          | trans (Const(@{const_syntax assign},_)$x$e) =
               (Const("_assign",dummyT) $ x $ translate_expression_back e
                handle ERROR _ => Const("_assign_quote",dummyT) $ x $ e)
          | trans (Const(@{const_syntax sample},_)$x$e) =
               (Const("_sample",dummyT) $ x $ translate_expression_back e
                handle ERROR _ => Const("_sample_quote",dummyT) $ x $ e)
          | trans (Const(@{const_syntax label},_)$l$p) =
               Const("_label",dummyT) $ Free(dest_string l,dummyT) $ trans p
          | trans (Const(@{const_syntax while},_)$e$p) =
               (Const("_while",dummyT) $ translate_expression_back e $ trans p
                handle ERROR _ => Const("_while_quote",dummyT) $ e $ trans p)
          | trans (Const(@{const_syntax ifte},_)$e$p$Const(@{const_syntax skip},_)) =
               (Const("_ifthen",dummyT) $ translate_expression_back e $ trans p
                handle ERROR _ => Const("_ifthen_quote",dummyT) $ e $ trans p)
          | trans (Const(@{const_syntax ifte},_)$e$p$q) =
               (Const("_ifte",dummyT) $ translate_expression_back e $ trans p $ trans q
                handle ERROR _ => Const("_ifte_quote",dummyT) $ e $ trans p $ trans q)
          | trans (Const(@{const_syntax seq},_)$p$q) =
               Const("_seq",dummyT) $ trans p $ trans q
          | trans p = Const("_quote",dummyT) $ p
    in trans p end
  end
*}

print_translation {* [(@{const_syntax program}, fn ctx => fn p => Const("_program",dummyT) $ translate_program_back ctx (hd p))] *};

end
