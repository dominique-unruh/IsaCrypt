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
    def vn == "freshvar used"
    def v == "\<lparr> vu_name=vn, vu_type=t, vu_global=False \<rparr>"
    def vs == "fresh_variables_local (v#used) ts"
    have v_vs: "fresh_variables_local used (t#ts) = v#vs"
      unfolding vs_def v_def vn_def by (auto simp: Let_def)
    from Cons.IH vs_def have vs_dist: "distinct vs" by auto
    from Cons.IH vs_def have unused: "\<forall>x\<in>set (v#used). x\<notin>set vs" by auto
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


record memory_rep = 
  mem_globals :: "variable_untyped \<Rightarrow> val"
  mem_locals :: "variable_untyped \<Rightarrow> val"
(*  mem_stack :: "(variable_untyped \<Rightarrow> val) list" *)

typedef memory = "{m::memory_rep. 
     (\<forall>v. mem_globals m v \<in> t_domain (vu_type v))
   \<and> (\<forall>v. mem_locals m v \<in> t_domain (vu_type v))
(*   \<and> (\<forall>s\<in>set (mem_stack m). \<forall>v. s v \<in> t_domain (vu_type v))*)}"
apply (rule exI[where x="\<lparr> mem_globals = (\<lambda>v. t_default (vu_type v)),
                           mem_locals = (\<lambda>v. t_default (vu_type v)) \<rparr>"])
  by auto

(*
typedef memory = "{(m::variable_untyped\<Rightarrow>val). (\<forall>v. m v \<in> t_domain (vu_type v))}"
  apply (rule exI[of _ "\<lambda>v. t_default (vu_type v)"], simp);
  by (metis Rep_type mem_Collect_eq t_default_def t_domain_def)
*)

definition "memory_lookup_untyped m v = (if vu_global v then mem_globals (Rep_memory m) v else mem_locals (Rep_memory m) v)"
definition "memory_update_untyped m v x = 
  (let m = Rep_memory m in
   let varval = if x\<in>t_domain(vu_type v) then x else t_default(vu_type v) in
   if vu_global v then
    Abs_memory (m\<lparr>mem_globals := (mem_globals m)(v:=varval)\<rparr>)
   else
    Abs_memory (m\<lparr>mem_locals := (mem_locals m)(v:=varval)\<rparr>))"
lemma memory_lookup_update_same_untyped: "a \<in> t_domain (vu_type v) \<Longrightarrow> memory_lookup_untyped (memory_update_untyped m v a) v = a"
  unfolding memory_lookup_untyped_def memory_update_untyped_def Let_def
  apply auto
  apply (subst Abs_memory_inverse, auto)
  using Rep_memory apply auto
  by (subst Abs_memory_inverse, auto)

lemma memory_lookup_update_notsame_untyped: 
  "v \<noteq> w \<Longrightarrow> memory_lookup_untyped (memory_update_untyped m v a) w = memory_lookup_untyped m w"
  SORRY

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
  apply (rule exI[of _ "\<lparr> edr_fun=\<lambda>m. 0,
                          edr_type=undefined,
                          edr_vars=[] \<rparr>"], simp)
  unfolding support_distr_def zero_distr_def
  apply (subst Abs_distr_inverse, auto)
  by (metis ereal_eq_0(2) ereal_less_eq(6) ereal_zero_mult zero_le_one)

definition "ed_fun e == edr_fun (Rep_expression_distr e)"
definition "ed_type e == edr_type (Rep_expression_distr e)"
definition "ed_vars e == edr_vars (Rep_expression_distr e)"

definition const_expression_untyped :: "type \<Rightarrow> val \<Rightarrow> expression_untyped" where
  "const_expression_untyped T x = Abs_expression_untyped \<lparr> eur_fun=\<lambda>m. x, eur_type=T, eur_vars=[] \<rparr>"

lemma eu_fun_const_expression_untyped: "a \<in> t_domain T \<Longrightarrow> eu_fun (const_expression_untyped T a) = (\<lambda>m. a)"
  unfolding const_expression_untyped_def eu_fun_def
  by (subst Abs_expression_untyped_inverse, auto)


type_synonym id0 = string
type_synonym id = "id0 list"

subsection {* Procedures *}

record procedure_type =
  pt_argtypes :: "type list"
  pt_returntype :: "type"

datatype program_rep =
  Assign variable_untyped expression_untyped
| Sample variable_untyped expression_distr
| Seq program_rep program_rep
| Skip
| IfTE expression_untyped program_rep program_rep
| While expression_untyped program_rep
| CallProc variable_untyped procedure_rep "expression_untyped list"
and procedure_rep =
  Proc program_rep "variable_untyped list" expression_untyped
| ProcRef nat (* deBruijn index *)
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
  "proctype_of (Proc body args return) = \<lparr> pt_argtypes=map vu_type args, pt_returntype=eu_type return \<rparr>"
| "proctype_of _ = undefined" (* Cannot happen for well-typed programs *)

subsection {* Well-typed programs *}

fun well_typed :: "program_rep \<Rightarrow> bool" where
  "well_typed (Seq p1 p2) = (well_typed p1 \<and> well_typed p2)"
| "well_typed (Assign v e) = (eu_type e = vu_type v)"
| "well_typed (Sample v e) = (ed_type e = vu_type v)"
| "well_typed Skip = True"
| "well_typed (While e p) = ((eu_type e = bool_type) \<and> well_typed p)"
| "well_typed (IfTE e thn els) = ((eu_type e = bool_type) \<and> well_typed thn \<and> well_typed els)"
| "well_typed (CallProc v (Proc body pargs ret) args) =
    (vu_type v = eu_type ret \<and> 
    map eu_type args = map vu_type pargs \<and>
    well_typed body \<and> (\<forall>v\<in>set pargs. \<not> vu_global v) \<and> distinct pargs)"
| "well_typed (CallProc v _ args) = False"

fun well_typed_proc :: "procedure_rep \<Rightarrow> bool" where
  "well_typed_proc (Proc body pargs ret) = 
    (well_typed body \<and> (\<forall>v\<in>set pargs. \<not> vu_global v) \<and> distinct pargs)"
| "well_typed_proc _ = False"

typedef program = "{prog. well_typed prog}"
  apply (rule exI[where x=Skip]) by simp
abbreviation "mk_program_untyped == Rep_program"

lemma well_typed_mk_program_untyped [simp]: "well_typed (mk_program_untyped x)" 
  using Rep_program by simp

subsection {* Denotational semantics *}

type_synonym denotation = "memory \<Rightarrow> memory distr"

fun while_iter :: "nat \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> denotation \<Rightarrow> memory \<Rightarrow> memory distr" where
  "while_iter 0 e p m = point_distr m"
| "while_iter (Suc n) e p m = 
      compose_distr (\<lambda>m. if e m then p m else 0)
                    (while_iter n e p m)"

definition "init_locals pargs args m = 
  (let args = map (\<lambda>e. eu_fun e m) args;
       m = Abs_memory (Rep_memory m\<lparr> mem_locals := (\<lambda>v. t_default (vu_type v)) \<rparr>) in
       fold (\<lambda>(v,x) m. memory_update_untyped m v x) (zip pargs args) m)"

definition 
 "restore_locals x oldmem newmem =
  memory_update_untyped
  (Abs_memory (Rep_memory newmem \<lparr> mem_locals := mem_locals (Rep_memory oldmem) \<rparr>))
  x (memory_lookup_untyped newmem x)"

fun denotation_untyped :: "program_rep \<Rightarrow> denotation" where
  denotation_untyped_Seq: "denotation_untyped (Seq p1 p2) m = compose_distr (denotation_untyped p2) (denotation_untyped p1 m)"
| denotation_untyped_Assign: "denotation_untyped (Assign v e) m = point_distr (memory_update_untyped m v (eu_fun e m))"
| denotation_untyped_Sample: "denotation_untyped (Sample v e) m = apply_to_distr (memory_update_untyped m v) (ed_fun e m)"
| denotation_untyped_Skip: "denotation_untyped (Skip) m = point_distr m"
| denotation_untyped_IfTE: "denotation_untyped (IfTE e thn els) m = (if (eu_fun e m = embedding True) then denotation_untyped thn m else denotation_untyped els m)"
| denotation_untyped_While: "denotation_untyped (While e p) m = 
    Abs_distr (\<lambda>m'. \<Sum>n. Rep_distr (compose_distr (\<lambda>m. if eu_fun e m = embedding True then 0 else point_distr m)
                                            (while_iter n (\<lambda>m. eu_fun e m = embedding True) (denotation_untyped p) m)) m')"
| denotation_untyped_CallProc: "denotation_untyped (CallProc v (Proc body pargs return) args) m = 
  apply_to_distr (restore_locals v m)
  (apply_to_distr (\<lambda>m. memory_update_untyped m v (eu_fun return m))
  (denotation_untyped body (init_locals pargs args m)))"
| denotation_untyped_CallProc_bad: "denotation_untyped (CallProc v _ args) m = 0" (* Cannot happen for well-typed programs *)
definition "denotation prog = denotation_untyped (mk_program_untyped prog)"

lemma denotation_untyped_assoc: "denotation_untyped (Seq (Seq x y) z) = denotation_untyped (Seq x (Seq y z))"
  unfolding denotation_untyped_Seq[THEN ext] 
  unfolding compose_distr_assoc ..

subsection {* Misc (free vars, lossless) *}

fun vars_untyped :: "program_rep \<Rightarrow> variable_untyped list" 
and vars_proc_untyped :: "procedure_rep \<Rightarrow> variable_untyped list" where
  "vars_untyped Skip = []"
| "vars_untyped (Seq p1 p2) = (vars_untyped p1) @ (vars_untyped p2)"
| "vars_untyped (Assign v e) = v # eu_vars e"
| "vars_untyped (Sample v e) = v # ed_vars e"
| "vars_untyped (IfTE e p1 p2) = eu_vars e @ vars_untyped p1 @ vars_untyped p2"
| "vars_untyped (While e p) = eu_vars e @ vars_untyped p"
| "vars_untyped (CallProc v proc args) = 
      v # [v. a\<leftarrow>args, v\<leftarrow>eu_vars a] @ vars_proc_untyped proc"
| "vars_proc_untyped (Proc body pargs return) =
      [v. v\<leftarrow>pargs, vu_global v] (* Empty for well-typed progs *)
      @ [v. v\<leftarrow>vars_untyped body, vu_global v]
      @ [v. v\<leftarrow>eu_vars return, vu_global v]"
| "vars_proc_untyped (ProcRef i) = []"
| "vars_proc_untyped (ProcAppl p q) = (vars_proc_untyped p) @ (vars_proc_untyped q)"
| "vars_proc_untyped (ProcAbs p) = vars_proc_untyped p"
| "vars_proc_untyped (ProcPair p q) = vars_proc_untyped p @ vars_proc_untyped q"
| "vars_proc_untyped (ProcUnpair _ p) = vars_proc_untyped p"

definition "vars prog = vars_untyped (mk_program_untyped prog)"

definition "lossless_untyped p = (\<forall>m. weight_distr (denotation_untyped p m) = 1)"
definition "lossless p = (\<forall>m. weight_distr (denotation p m) = 1)"


end
