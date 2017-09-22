theory Modules
  imports Universe TypedLambda "HOL-Library.Multiset"
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

  
definition "Type (_::('a::prog_type) itself) 
    = Abs_type \<lparr> tr_domain=range (embedding::'a\<Rightarrow>val),
                 tr_default=embedding (default::'a) \<rparr>"
lemma Rep_type_Type: "Rep_type (Type (T::'a::prog_type itself)) = 
               \<lparr> tr_domain=range (embedding::'a\<Rightarrow>val),
                 tr_default=embedding (default::'a) \<rparr>"
  unfolding Type_def by (subst Abs_type_inverse, auto)


record procedure_type =
  pt_argtype :: "type"
  pt_returntype :: "type"

datatype 'a procedure =
  Proc 'a
| ProcRef nat (* deBruijn index *)
| ProcUnit
| ProcAbs "'a procedure"
| ProcAppl "'a procedure" "'a procedure"
| ProcPair "'a procedure" "'a procedure"
| ProcUnpair bool "'a procedure" (* ProcUnpair True = fst, ProcUnpair False = snd *)

datatype lambda = 
  Abs lambda | Nat nat | Plus lambda lambda | Invoke "lambda procedure"


(* record (overloaded) ('a,'b,'c) procedure = 
  p_body :: 'a
  p_arg :: 'b
  p_return :: 'c *)


datatype procedure_type_open = 
   ProcTSimple procedure_type
 | ProcTFun procedure_type_open procedure_type_open
 | ProcTPair procedure_type_open procedure_type_open
 | ProcTUnit

locale modules =
  (* 'program = type of programs *)
  fixes well_typed_program :: "(procedure_type_open list \<Rightarrow> 'program procedure \<Rightarrow> procedure_type_open \<Rightarrow> bool)
                             \<Rightarrow> procedure_type_open list \<Rightarrow> 'program \<Rightarrow> procedure_type \<Rightarrow> bool"
    (* and proc_map :: "('program procedure \<Rightarrow> 'program procedure) \<Rightarrow> 'program \<Rightarrow> 'program" *)
(* proc_map can be implemented using proc_update *)
    and proc_list :: "'program \<Rightarrow> 'program procedure list"
    and proc_size :: "'program procedure \<Rightarrow> nat"
    (* and proc_relation :: "('program procedure \<Rightarrow> 'program procedure \<Rightarrow> bool) \<Rightarrow> 'program \<Rightarrow> 'program \<Rightarrow> bool" *)
(* proc_relation can be implemented using proc_update *)
    (* and proc_update :: "'program \<Rightarrow> nat \<Rightarrow> 'program procedure \<Rightarrow> 'program" (* proc_update can be written using proc_update' *) *)
    and proc_update' :: "'program \<Rightarrow> 'program procedure list \<Rightarrow> 'program"
  assumes proc_size_Proc: "y \<in> set (proc_list x) \<Longrightarrow> proc_size y < proc_size (Proc x)" 
      and proc_size_ProcAppl[simp]: "proc_size (ProcAppl s t) = proc_size s + proc_size t + 1"
      and proc_size_ProcPair[simp]: "proc_size (ProcPair s t) = proc_size s + proc_size t + 1"
      and proc_size_ProcUnpair[simp]: "proc_size (ProcUnpair b s) = proc_size s + 1"
      and proc_size_ProcAbs[simp]: "proc_size (ProcAbs s) = proc_size s + 1"
      (* and proc_map_cong[fundef_cong]: "p=q \<Longrightarrow> (\<And>z. proc_size z < proc_size (Proc q) \<Longrightarrow> f z = g z) \<Longrightarrow> proc_map f p = proc_map g q" *)
      (* and proc_map_cong[fundef_cong]: "p=q \<Longrightarrow> (\<And>z. z \<in> set (proc_list q) \<Longrightarrow> f z = g z) \<Longrightarrow> proc_map f p = proc_map g q" *)
      (* and proc_list_map: "proc_list (proc_map f p) = map f (proc_list p)" *)
      (* and proc_map_proc_map [simp]: "proc_map f (proc_map g p) = proc_map (\<lambda>x. f (g x)) p" *)
      (* and proc_map_id[simp]: "proc_map (\<lambda>x. x) p = p" *)
(* and well_typed_program_cong[fundef_cong]: "\<lbrakk>E=E'; pg=pg'; T=T'; \<And>pc. pc\<in>set(proc_list pg') \<Longrightarrow> wt E' pc (ProcTSimple T') = wt' E' pc (ProcTSimple T')\<rbrakk>
                   \<Longrightarrow> well_typed_program wt E pg T = well_typed_program wt' E' pg' T'" *)
      and well_typed_program_mono[mono]: "wt \<le> wt' \<Longrightarrow> well_typed_program wt E p T \<longrightarrow> well_typed_program wt' E p T"
      and well_typed_program_simple: "well_typed_program wt E p T \<Longrightarrow> \<forall>pc\<in>set(proc_list pc). \<exists>T'. wt E pc (ProcTSimple T')"
      (* and proc_relation_mono[mono]: "R \<le> R' \<Longrightarrow> proc_relation R \<le> proc_relation R'" *)
      (* and proc_update_list: "proc_list (proc_update p i y) = proc_list p[i:=y]" *)
      (* and proc_relation_eq[simp]: "proc_relation (op=) p q = (p=q)" *)
      (* and proc_relation_cong[fundef_cong]: "\<lbrakk>p=p'; q=q'; \<And>z z'. (z,z')\<in>set(zip (proc_list p) (proc_list q)) \<Longrightarrow> R z z' = R' z z'\<rbrakk> \<Longrightarrow> proc_relation R p q = proc_relation R' p' q'" *)
      and proc_update'_list: "length l = length (proc_list proc) \<Longrightarrow> proc_list (proc_update' proc l) = l"
      and proc_update'_self[simp]: "proc_update' proc (proc_list proc) = proc"
      and proc_update'_twice[simp]: "proc_update' (proc_update' proc l) l' = proc_update' proc l'"
begin


definition "same_shape s t = (length (proc_list s) = length (proc_list t) \<and> s = proc_update' t (proc_list s))"


definition "proc_map f p = proc_update' p (map f (proc_list p))"

lemma proc_map_cong[fundef_cong]: "p=q \<Longrightarrow> (\<And>z. z \<in> set (proc_list q) \<Longrightarrow> f z = g z) \<Longrightarrow> proc_map f p = proc_map g q"
  unfolding proc_map_def apply auto
  by (metis map_eq_conv)

lemma proc_list_map: "proc_list (proc_map f p) = map f (proc_list p)"
  unfolding proc_map_def
  by (simp add: proc_update'_list) 

lemma same_shape_refl[simp]: "same_shape x x"
  unfolding same_shape_def
  using proc_update'_self by auto

lemma same_shape_list: 
 "same_shape p q \<and> proc_list p = proc_list q \<longleftrightarrow> p = q" 
proof (rule)
  assume "same_shape p q \<and> proc_list p = proc_list q"
  hence "p = proc_update' q (proc_list q)" and "proc_list p = proc_list q" unfolding same_shape_def by auto
  then show "p=q" 
    by simp
next
  assume "p=q"
  then show "same_shape p q \<and> proc_list p = proc_list q"
    by simp
qed

lemma same_shape_trans[trans]: assumes "same_shape a b" and "same_shape b c" shows "same_shape a c" 
proof -
  have a: "a = proc_update' b (proc_list a)" and b: "b = proc_update' c (proc_list b)"
    using assms unfolding same_shape_def by auto
  have len: "length (proc_list a) = length (proc_list c)" 
    using assms unfolding same_shape_def by auto
  moreover have "a = proc_update' c (proc_list a)" 
    apply (subst a, subst b) 
    by simp
  ultimately show ?thesis
    unfolding same_shape_def
    by simp
qed

lemma same_shape_sym[sym]: assumes "same_shape a b" shows "same_shape b a"
proof -
  have a: "a = proc_update' b (proc_list a)"
    using assms unfolding same_shape_def by auto
  have "b = proc_update' a (proc_list b)"
    apply (subst a) by simp
  then show ?thesis
    using assms
    unfolding same_shape_def
    by simp
qed

lemma same_shape_update'L[simp]: "length (proc_list p) = length l \<Longrightarrow> same_shape (proc_update' p l) p"
  unfolding same_shape_def
  by (simp add: proc_update'_list)

lemma same_shape_update'R[simp]: "length (proc_list p) = length l \<Longrightarrow> same_shape p (proc_update' p l)"
  unfolding same_shape_def
  by (simp add: proc_update'_list)

lemma same_shape_mapL[simp]: "same_shape (proc_map f p) p"
  unfolding proc_map_def by simp

lemma same_shape_mapR[simp]: "same_shape p (proc_map f p)"
  unfolding proc_map_def by simp

lemma proc_map_proc_map [simp]: "proc_map f (proc_map g p) = proc_map (\<lambda>x. f (g x)) p"
proof -
  have list: "proc_list (proc_map f (proc_map g p)) = proc_list (proc_map (\<lambda>x. f (g x)) p)"
    apply (subst proc_list_map)+ by auto
  have "same_shape (proc_map f (proc_map g p)) (proc_map g p)" by simp
  also have "same_shape \<dots> p" by simp
  also have "same_shape \<dots> (proc_map (\<lambda>x. f (g x)) p)" by simp
  finally have shape: "same_shape (proc_map f (proc_map g p)) (proc_map (\<lambda>x. f (g x)) p)"  by simp
  from list shape show ?thesis
    apply (subst same_shape_list[symmetric]) by simp
qed

lemma proc_map_id[simp]: "proc_map (\<lambda>x. x) p = p"
  unfolding proc_map_def by simp

abbreviation "proc_set proc \<equiv> set (proc_list proc)"

abbreviation "proc_length proc \<equiv> length (proc_list proc)"

definition "proc_update p i y = (proc_update' p (proc_list p[i:=y]))"

lemma proc_update_list: "proc_list (proc_update p i y) = proc_list p[i:=y]"
  unfolding proc_update_def 
  apply (rule proc_update'_list) by simp

definition "proc_relation R s t = (same_shape s t \<and> list_all2 R (proc_list s) (proc_list t))"

lemma proc_relation_mono[mono]: assumes "R \<le> R'" shows "proc_relation R \<le> proc_relation R'"
  unfolding proc_relation_def using assms list_all2_mono predicate2D by fastforce

(*definition "proc_relation_nth R i s t = (i < length (proc_list s) \<and>
   t = proc_update s i (nth (proc_list t) i) \<and> R (nth (proc_list s) i) (nth (proc_list t) i))"*)

definition "proc_relation_nth R i s t = (same_shape s t \<and> i < proc_length s \<and> (proc_list t = proc_list s[i:=proc_list t!i]) \<and> R (proc_list s!i) (proc_list t!i))"

lemma proc_relation_nth_mono[mono]:
  assumes "R \<le> R'"
  shows "proc_relation_nth R i \<le> proc_relation_nth R' i"
  using assms unfolding proc_relation_nth_def by auto



(* definition "subterm_relation = {(p,q) | p q r . q \<in> proc_set r \<and> r \<in> program_set (p::'program procedure) }" *)
(* lemma wf_subterm_relation[simp]: "wf subterm_relation" using proc_set_wellfounded unfolding subterm_relation_def . *)


inductive well_typed :: "procedure_type_open list \<Rightarrow> 'program procedure \<Rightarrow> procedure_type_open \<Rightarrow> bool"
  where wt_ProcRef: "i<length E \<Longrightarrow> E!i = T \<Longrightarrow> well_typed E (ProcRef i) T"
| wt_ProcAppl: "well_typed E p (ProcTFun T U) \<Longrightarrow>
  well_typed E q T \<Longrightarrow>
  well_typed E (ProcAppl p q) U"
| wt_ProcAbs: "well_typed (T#E) p U \<Longrightarrow> well_typed E (ProcAbs p) (ProcTFun T U)"
| wt_ProcPair: "well_typed E p T \<Longrightarrow> well_typed E q U \<Longrightarrow> well_typed E (ProcPair p q) (ProcTPair T U)"
| wt_ProcUnpair: "well_typed E p (ProcTPair T U) \<Longrightarrow> well_typed E (ProcUnpair b p) (if b then T else U)"
| wt_ProcUnit: "well_typed E ProcUnit ProcTUnit"
| wt_Proc: "well_typed_program well_typed E p T \<Longrightarrow> well_typed E (Proc p) (ProcTSimple T)"

   

function lift_proc :: "['program procedure, nat] \<Rightarrow> 'program procedure" where
  lift_proc_Proc: "lift_proc (Proc p) k = Proc (proc_map (\<lambda>p. lift_proc p k) p)"
| lift_proc_ProcRef: "lift_proc (ProcRef i) k = (if i < k then ProcRef i else ProcRef (Suc i))"
| lift_proc_ProcAppl: "lift_proc (ProcAppl s t) k = ProcAppl (lift_proc s k) (lift_proc t k)"
| lift_proc_ProcPair: "lift_proc (ProcPair s t) k = ProcPair (lift_proc s k) (lift_proc t k)"
| lift_proc_ProcUnpair: "lift_proc (ProcUnpair b s) k = ProcUnpair b (lift_proc s k)"
| lift_proc_ProcAbs: "lift_proc (ProcAbs s) k = ProcAbs (lift_proc s (Suc k))"
| lift_proc_ProcUnit: "lift_proc ProcUnit k = ProcUnit"
  by pat_completeness auto
termination apply (relation "measure (\<lambda>(p,k). proc_size p)") 
  using proc_size_Proc by auto

function subst_proc :: "[nat, 'program procedure, 'program procedure] \<Rightarrow> 'program procedure"
where
  subst_proc_Proc: "subst_proc i p (Proc pg) =
     Proc (proc_map (subst_proc i p) pg)"
| subst_proc_ProcRef: "subst_proc k s (ProcRef i) = 
      (if k < i then ProcRef (i - 1) else if i=k then s else ProcRef i)"
| subst_proc_ProcAppl: "subst_proc k s (ProcAppl t u) = ProcAppl (subst_proc k s t) (subst_proc k s u)"
| subst_proc_ProcPair: "subst_proc k s (ProcPair t u) = ProcPair (subst_proc k s t) (subst_proc k s u)"
| subst_proc_ProcUnpair: "subst_proc k s (ProcUnpair b t) = ProcUnpair b (subst_proc k s t)"
| subst_proc_ProcAbs: "subst_proc k s (ProcAbs t) = ProcAbs (subst_proc (Suc k) (lift_proc s 0) t)"
| subst_proc_ProcUnit: "subst_proc k s ProcUnit = ProcUnit"
  by pat_completeness auto
termination apply (relation "measure (\<lambda>(_,_,p). proc_size p)") 
  using proc_size_Proc by auto

lemma procedure_induct[case_names Proc ProcRef ProcUnit ProcAbs ProcAppl ProcPair ProcUnpair]:
  assumes proc: "\<And>pg. (\<And>p. p \<in> proc_set pg \<Longrightarrow> P p) \<Longrightarrow> P (Proc pg)"
    and "\<And>p. P (ProcRef p)"
    and "P ProcUnit "
    and procabs: "(\<And>p. P p \<Longrightarrow> P (ProcAbs p))"
    and procappl: "(\<And>a b. P a \<Longrightarrow> P b \<Longrightarrow> P (ProcAppl a b))"
    and procpair: "(\<And>a b. P a \<Longrightarrow> P b \<Longrightarrow> P (ProcPair a b))"
    and procunpair: "(\<And>b p. P p \<Longrightarrow> P (ProcUnpair b p))"
  shows "P proc"
proof (induct n\<equiv>"proc_size proc" arbitrary: proc rule:nat_less_induct)
  case 1
  hence "P p" if "proc_size p < proc_size proc" for p
    using that by blast
  show ?case
  proof (cases proc)
    case (Proc pg)
    then show ?thesis
      using 1 proc proc_size_Proc by blast
  next
    case (ProcAbs x4)
    then show ?thesis 
      using 1 procabs proc_size_ProcAbs by auto
  next
    case (ProcAppl a b)
    then show ?thesis 
      using 1 procappl proc_size_ProcAppl
      by (metis (no_types, lifting) Nat.add_0_right One_nat_def add_Suc_right lessI lift_Suc_mono_less_iff trans_less_add2 zero_less_Suc)
  next
    case (ProcPair x61 x62)
    then show ?thesis 
      using 1 procpair proc_size_ProcPair
      by (metis add.commute add_lessD1 less_add_one)
  next
    case (ProcUnpair x71 x72)
    then show ?thesis apply auto
      using 1 procunpair proc_size_ProcUnpair by auto
  qed (auto simp: assms)
qed


lemma lift_lift:
  assumes "i < k + 1"
  shows "lift_proc (lift_proc t i) (Suc k) = lift_proc (lift_proc t k) i"
proof (insert assms, induction t arbitrary: i k rule:procedure_induct)
  case (Proc p pg)
  show ?case 
    apply auto
    apply (rule proc_map_cong)
    using Proc by auto
qed auto

lemma lift_subst [simp]:
  assumes "j < Suc i"
  shows "lift_proc (subst_proc j s t) i = subst_proc j (lift_proc s i) (lift_proc t (Suc i))"
proof (insert assms, induction t arbitrary: i j s rule:procedure_induct)
  case (Proc p pg)
  show ?case 
    apply auto
    apply (rule proc_map_cong)
    using Proc by auto
next
  case (ProcAbs p)
  then show ?case 
    by (simp add: diff_Suc lift_lift split: nat.split)
qed auto

lemma lift_subst_lt:
  assumes "i < j + 1"
  shows "lift_proc (subst_proc j s t) i = subst_proc (j+1) (lift_proc s i) (lift_proc t i)"
proof (insert assms, induction t arbitrary: i j s rule:procedure_induct)
  case (Proc p pg)
  show ?case 
    apply auto
    apply (rule proc_map_cong)
    using Proc by auto
next
  case (ProcAbs p)
  then show ?case 
    by (simp add: lift_lift)
qed auto

lemma subst_lift [simp]:
  shows "subst_proc k s (lift_proc t k) = t"
proof (induction t arbitrary: k s rule:procedure_induct)
  case (Proc p pg)
  show ?case 
    apply auto
    apply (rewrite in "_=\<hole>" proc_map_id[symmetric])
    apply (rule proc_map_cong)
    using Proc by auto
qed auto


lemma subst_subst:
  assumes "i < Suc j"
  shows "subst_proc i (subst_proc j v u) (subst_proc (Suc j) (lift_proc v i) q) = subst_proc j v (subst_proc i u q)"
proof (insert assms, induction q arbitrary: i j u v rule:procedure_induct)
  case (Proc pg)
  then show ?case 
    apply auto 
    apply (rule proc_map_cong)
    using Proc by auto
next
  case (ProcAbs p)
  then show ?case 
    by (simp_all add: diff_Suc lift_lift [symmetric] lift_subst_lt split: nat.split)
qed auto

end

locale beta_reduce_proofs = typed_lambda + modules 
  (* fixes prog_to_dB :: "'a \<Rightarrow> dB" (* Should be constructed *) *)
begin

(* definition prog_to_dB :: "'a \<Rightarrow> dB" where
  "prog_to_dB p = fold (\<lambda>dB pc \<Rightarrow> dB \<degree> pc) Proc0 (proc_list p)" *)

abbreviation "Proc0 == Abs(Var 0)"

function proc_to_dB :: "'a procedure \<Rightarrow> dB" where
  proc_to_dB_Proc: "proc_to_dB (Proc p) = (foldl (\<lambda>(dB::dB) pc. (Abs(Abs(Var 0))) \<degree> dB \<degree> (proc_to_dB pc)) Proc0 (proc_list p))" 
| "proc_to_dB (ProcRef i) = Var i"
| "proc_to_dB (ProcAbs p) = Abs (proc_to_dB p)"
| "proc_to_dB (ProcAppl p q) = proc_to_dB p \<degree> proc_to_dB q"
| "proc_to_dB (ProcPair p q) = MkPair (proc_to_dB p) (proc_to_dB q)"
| "proc_to_dB (ProcUnpair b p) = Unpair b (proc_to_dB p)"
| "proc_to_dB ProcUnit = Proc0"
  by pat_completeness auto
termination apply (relation "measure proc_size") using proc_size_Proc by auto 

lemma proc_to_dB_lift [iff]:
  shows   "proc_to_dB (lift_proc q k) = lift (proc_to_dB q) k"
proof (induction rule:lift_proc.induct)
  case (1 p k) (* Proc *) 
  define app where "app = (\<lambda>(dB::dB) pc.  (Abs(Abs(Var 0))) \<degree> dB \<degree> proc_to_dB pc)"
  define pl where "pl = proc_list p"
  define P0 where "P0 = Proc0"
  have app_lift: "app (lift a k) (lift_proc x k) = lift (app a x) k" if "x \<in> proc_set p" for a x
    unfolding app_def using that 1 by auto
  have x_pl: "x \<in> proc_set p" if "x\<in>set pl" for x
    using pl_def that by simp

  have "proc_to_dB (lift_proc (Proc p) k) = foldl app P0 (proc_list (proc_map (\<lambda>p. lift_proc p k) p))"
    unfolding app_def P0_def by simp
  also have "\<dots> = foldl app P0 (map (\<lambda>p. lift_proc p k) pl)"
    using proc_list_map pl_def by simp
  also have "\<dots> = lift (foldl app P0 pl) k"
    apply (insert x_pl, induction pl rule:rev_induct)
     using P0_def apply simp
    using app_lift by simp
  also have "\<dots> = lift (proc_to_dB (Proc p)) k" 
    unfolding app_def P0_def pl_def by simp
  finally show ?case .
qed auto

lemma proc_to_dB_subst [iff]:
   "proc_to_dB (subst_proc k x q) = proc_to_dB q[proc_to_dB x/k]"
proof (induction arbitrary: k x rule:procedure_induct)
  case (Proc pg)
  define f and start where "f dB pc = ((Abs(Abs(Var 0))) \<degree> dB \<degree> proc_to_dB pc)" and "start = (dB.Abs (dB.Var 0))" for dB pc
  define pl where "pl = proc_list pg"
  then have pl: "set pl \<subseteq> proc_set pg" by simp
  have "foldl f start (map (subst_proc k x) pl) = foldl f start pl[proc_to_dB x/k]" 
  proof (insert pl, induction pl rule:rev_induct)
    case Nil
    then show ?case unfolding start_def by simp
  next
    case (snoc a pl)
    hence a_pg: "a \<in> proc_set pg" by simp
    have "f (foldl f start pl) a[proc_to_dB x/k] = (Abs(Abs(Var 0))) \<degree>foldl f start pl[proc_to_dB x/k] \<degree> proc_to_dB a[proc_to_dB x/k]"
      unfolding f_def by simp 
    also have "\<dots> = (Abs(Abs(Var 0))) \<degree> foldl f start (map (subst_proc k x) pl) \<degree> proc_to_dB a[proc_to_dB x/k]" 
      using snoc by simp
    also have "\<dots> = (Abs(Abs(Var 0))) \<degree> foldl f start (map (subst_proc k x) pl) \<degree> proc_to_dB (subst_proc k x a)"
      by (subst Proc[OF a_pg], simp)
    also have "\<dots> = f (foldl f start (map (subst_proc k x) pl)) (subst_proc k x a)" unfolding f_def by simp
    finally show ?case by simp
  qed
  then show ?case 
    unfolding subst_proc_Proc proc_to_dB_Proc proc_list_map f_def start_def pl_def by simp
qed auto

abbreviation "ProcT == Fun (Atom 0) (Atom 0)"

fun typ_conv :: "procedure_type_open \<Rightarrow> lambda_type" where
  "typ_conv (ProcTSimple _) = ProcT"
| "typ_conv ProcTUnit = ProcT"
| "typ_conv (ProcTFun T U) = Fun (typ_conv T) (typ_conv U)"
| "typ_conv (ProcTPair T U) = Prod (typ_conv T) (typ_conv U)"

lemma typ_pres:
  assumes "well_typed E p T"
  shows "(\<lambda>i. typ_conv (E!i)) \<turnstile> proc_to_dB p : typ_conv T"
  apply (insert assms)
proof (induction n\<equiv>"proc_size p" arbitrary: E p T rule:nat_less_induct[case_names induct_n])
  case induct_n
  hence IH: "proc_size q < proc_size p \<Longrightarrow>
           well_typed E q T \<Longrightarrow> (\<lambda>i. typ_conv (E!i)) \<turnstile> proc_to_dB q : typ_conv T"
    for q E T
    by auto

  from induct_n have wt_EpT: "well_typed E p T" ..
  define E' where "E' = (\<lambda>i. beta_reduce_proofs.typ_conv (E ! i))"
  from wt_EpT show ?case
  proof cases
    case (wt_ProcAppl p' T' q')
    hence aux: "(\<lambda>i. beta_reduce_proofs.typ_conv (E ! i)) \<turnstile> proc_to_dB p' : typ_conv (ProcTFun T' T)"
      apply (rule_tac IH) by auto
    show ?thesis 
      unfolding wt_ProcAppl
      apply simp
      apply (rule typed_lambda.App)
      using wt_ProcAppl 
      using aux close
      apply (rule IH)
      using wt_ProcAppl by auto
  next
    case (wt_ProcAbs T p U)
    have shift: "(\<lambda>i. beta_reduce_proofs.typ_conv (E ! i))<0:beta_reduce_proofs.typ_conv T> =
             (\<lambda>i. beta_reduce_proofs.typ_conv ((T#E) ! i))" by (auto simp: shift_def)
    show ?thesis unfolding wt_ProcAbs
      apply simp
      apply (rule typed_lambda.Abs)
      apply (subst shift)
      apply (rule IH)
      using wt_ProcAbs by auto
  next
    case (wt_ProcPair p T q U)
    show ?thesis
      unfolding wt_ProcPair
      apply simp
      apply (rule typed_lambda.MkPair)
       apply (rule IH)
      using wt_ProcPair close 2
      apply (rule IH)
      using wt_ProcPair by auto
  next
    case (wt_ProcUnpair p T U b)
    have aux: "(\<lambda>i. beta_reduce_proofs.typ_conv (E ! i)) \<turnstile> proc_to_dB p : (beta_reduce_proofs.typ_conv (ProcTPair T U))"
      apply (rule IH)
      using wt_ProcUnpair by auto
    show ?thesis 
      unfolding wt_ProcUnpair
      apply (cases b)
       apply simp
       apply (rule typed_lambda.Fst)
      using aux close simp
      apply simp
      apply (rule typed_lambda.Snd)
      using aux by simp
  next
    case (wt_Proc p' T')
    define E' where "E' = (\<lambda>i. beta_reduce_proofs.typ_conv (E ! i))"
    define pl where "pl = proc_list p'"
    define start where "start =  (dB.Abs (dB.Var 0))"
    hence startT: "E' \<turnstile> start: ProcT" by auto
    have wt_Proc': "well_typed_program well_typed E p' T'"
      apply (rule well_typed_program_mono[THEN mp, rotated])
       apply (fact wt_Proc)
      by (simp add: le_funI)
    have plT: "E' \<turnstile> proc_to_dB p1 : ProcT" if p1pl: "p1 \<in> set pl" for p1
    proof -
      obtain U where U: "well_typed E p1 (ProcTSimple U)"
        apply atomize_elim apply (rule well_typed_program_simple[THEN bspec])
         apply (fact wt_Proc')
        using p1pl unfolding pl_def by simp
      have size: "proc_size p1 < proc_size p"
        using local.wt_Proc(1) pl_def proc_size_Proc that by blast
      have "E' \<turnstile> proc_to_dB p1 : typ_conv (ProcTSimple U)"
        unfolding E'_def using size U by (rule IH)
      then show ?thesis by auto
    qed
    have "E' \<turnstile> foldl (\<lambda>dB pc. (Abs(Abs(Var 0))) \<degree> dB \<degree> proc_to_dB pc) start pl : Atom 0 \<Rightarrow> Atom 0" 
    proof (insert startT plT, induction pl arbitrary: start)
      case Nil
      then show ?case by simp
    next
      case (Cons p1 ps)
      have start_p1_T: "E' \<turnstile> (Abs(Abs(Var 0))) \<degree> start \<degree> proc_to_dB p1 : Atom 0 \<Rightarrow> Atom 0"
        apply (rule typed_lambda.App[where T=ProcT])
         apply (rule typed_lambda.App[where T=ProcT])
          close (rule typed_lambda.Abs, rule typed_lambda.Abs, rule typed_lambda.Var, simp)
         apply (rule Cons)+
        by simp
      show ?case
        apply simp
        apply (rule Cons.IH)
        using  start_p1_T Cons.prems by auto
    qed

    then show ?thesis
      unfolding start_def E'_def pl_def wt_Proc by auto
  qed auto
qed



inductive beta_reduce_proc :: "'a procedure \<Rightarrow> 'a procedure \<Rightarrow> bool" where
  br_Proc: "proc_relation_nth beta_reduce_proc i s t \<Longrightarrow> beta_reduce_proc (Proc s) (Proc t)"
| br_beta: "beta_reduce_proc (ProcAppl (ProcAbs s) t) (subst_proc 0 t s)"
| br_ProcAppl1: "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcAppl s u) (ProcAppl t u)"
| br_ProcAppl2: "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcAppl u s) (ProcAppl u t)"
| br_ProcAbs: "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcAbs s) (ProcAbs t)"
| br_ProcPair1: "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcPair s u) (ProcPair t u)"
| br_ProcPair2: "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcPair u s) (ProcPair u t)"
| br_ProcUnpair: "beta_reduce_proc s t \<Longrightarrow> beta_reduce_proc (ProcUnpair b s) (ProcUnpair b t)"
| br_ProcUnpairPair: "beta_reduce_proc (ProcUnpair b (ProcPair s t)) (if b then s else t)"


inductive_cases
    brc_Proc: "beta_reduce_proc (Proc p) u"
and brc_ProcAppl: "beta_reduce_proc (ProcApply p1 p2) u"
and brc_ProcAbs: "beta_reduce_proc (ProcAbs p) u"
and brc_ProcPair: "beta_reduce_proc (ProcPair p1 p2) u"
and brc_ProcUnpair: "beta_reduce_proc (ProcUnpair b p) u"
and brc_ProcRef: "beta_reduce_proc (ProcRef i) u"
and brc_ProcUnit: "beta_reduce_proc ProcUnit u"



lemma accp_map: 
  assumes "Wellfounded.accp R (f z)"
  shows "Wellfounded.accp (\<lambda>x y. R (f x) (f y)) z"
proof -
  {fix x have "Wellfounded.accp R x \<Longrightarrow> x=f z 
     \<Longrightarrow> Wellfounded.accp (\<lambda>x y. R (f x) (f y)) z"
     apply (induction  arbitrary: z rule:Wellfounded.accp.induct)
     by (metis not_accp_down)}
  with assms show ?thesis by auto
qed

lemma termip_map: 
  assumes "termip R (f z)"
  shows "termip (\<lambda>x y. R (f x) (f y)) z"
proof -
  {fix x have "termip R x \<Longrightarrow> x=f z 
     \<Longrightarrow> termip (\<lambda>x y. R (f x) (f y)) z"
     apply (induction  arbitrary: z rule:Wellfounded.accp.induct, auto)
     by (metis (no_types, lifting) conversep_iff not_accp_down)}
  with assms show ?thesis by auto
qed

lemma rev_list_induct2 [consumes 1, case_names Nil snoc]:
  assumes len: "length xs = length ys" and Nil: "P [] []"
    and snoc: "(\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs@[x]) (ys@[y]))"
  shows "P xs ys"
proof -
  define P' where "P' xs ys = P (rev xs) (rev ys)" for xs ys
  define rxs rys where "rxs = rev xs" and "rys = rev ys" 
  have "length rxs = length rys" using len unfolding rxs_def rys_def by simp
  hence "P' rxs rys" 
    apply (induction rule:list_induct2)
    unfolding P'_def using Nil apply simp
    using snoc by simp
  thus ?thesis
    unfolding P'_def rxs_def rys_def by simp
qed

lemma well_typed_beta_reduce:
  assumes wt: "well_typed E p T"
  shows "termip beta_reduce_proc p"
proof -
  define beta2 where "beta2 == \<lambda>p q. (proc_to_dB p) \<rightarrow>\<^sub>\<beta> (proc_to_dB q)"

  have rel: "beta_reduce_proc q1 q2 \<Longrightarrow> beta2 q1 q2" for q1 q2
    unfolding beta2_def
  proof (induction rule:beta_reduce_proc.induct)
    case (br_Proc i s t)
    define f and start and j and sl tl and sj tj
      where "f = (\<lambda>dB pc. dB.Abs (dB.Abs (dB.Var 0)) \<degree> dB \<degree> proc_to_dB pc)"
      and "start = Abs (Var 0)"
      and "j = length (proc_list s) - i - 1"
      and "sl = rev (proc_list s)" and "tl = rev (proc_list t)"
      and "sj = sl ! j" and "tj = tl ! j"
    from br_Proc have i_sl: "i < length (proc_list s)" unfolding proc_relation_nth_def by simp
    from br_Proc  have tmp: "t = proc_update s i (proc_list t ! i)" unfolding proc_relation_nth_def
      by (metis modules.proc_update_def modules_axioms same_shape_def same_shape_sym)
    hence len': "length (proc_list s) = length (proc_list t)"
      by (metis length_list_update proc_update_list)
    hence len: "length sl = length tl" unfolding sl_def tl_def by simp
    have "proc_list t = proc_list s[i:=proc_list t!i]"
      apply (subst tmp)  unfolding proc_update_list by simp
    hence tl_sl: "tl = sl[j:=tj]"
      unfolding proc_relation_nth_def sl_def tj_def j_def 
      apply (subst rev_update[symmetric])
      using i_sl close
      unfolding tl_def len' 
      apply (subst rev_nth)
      using i_sl len' by auto
    from i_sl have j_sl: "j < length sl"
      unfolding j_def sl_def by auto
    from br_Proc have "proc_to_dB (proc_list s!i) \<rightarrow>\<^sub>\<beta> proc_to_dB (proc_list t!i)"
      unfolding proc_relation_nth_def unfolding sj_def tj_def sl_def tl_def by auto
    hence sj_tj_beta: "proc_to_dB sj \<rightarrow>\<^sub>\<beta> proc_to_dB tj"
      unfolding sj_def tj_def j_def sl_def tl_def using i_sl apply auto 
      apply (subst rev_nth) using i_sl close
      apply (subst rev_nth) using i_sl len' close
      using len' by auto
    have "foldr (\<lambda>x y. f y x) sl start \<rightarrow>\<^sub>\<beta> foldr (\<lambda>x y. f y x) tl start"
      using len 
    proof (insert j_sl tl_sl sj_def, induction arbitrary: j rule:list_induct2)
      case Nil then show ?case by simp
    next
      case (Cons s0 sl t0 tl)
      show ?case
      proof (cases j)
        case 0
        with Cons have "t0=tj"
          by (metis nth_Cons_0 nth_list_update_eq)
        from 0 Cons have "s0=sj"
          by (metis nth_Cons')
        from Cons 0 have "tl=sl"
          by (metis list.inject list_update_code(2))
        have fax: "f a s0 \<rightarrow>\<^sub>\<beta> f a t0" for a
          unfolding f_def \<open>t0=tj\<close> \<open>s0=sj\<close> apply (rule appR) using sj_tj_beta by auto
        show ?thesis apply simp
          unfolding \<open>tl=sl\<close> by (rule fax)
      next
        case (Suc j')
        with Cons have "s0=t0"
          by (metis list_update_code(3) nth_Cons_0)
        have fax: "f a x \<rightarrow>\<^sub>\<beta> f b x" if "a \<rightarrow>\<^sub>\<beta> b" for a b x
          unfolding f_def using that by auto
        have foldf: "foldr (\<lambda>x y. f y x) sl start \<rightarrow>\<^sub>\<beta> foldr (\<lambda>x y. f y x) tl start"
          apply (rule Cons.IH[where j=j'])
          using Cons.prems Suc by auto
        show ?thesis
          apply simp unfolding \<open>s0=t0\<close> using foldf by (rule fax)
      qed
    qed
    then show ?case
      unfolding foldr_conv_foldl sl_def tl_def start_def f_def by simp
  qed auto

  show "termip beta_reduce_proc p"
  proof -
    have leq: "beta_reduce_proc \<le> beta2" by (auto simp: rel)
    have termip_leq: "termip beta2 \<le> termip beta_reduce_proc"
      by (rule accp_subset, simp add: leq)
    have "(\<lambda>i. typ_conv (E!i)) \<turnstile> proc_to_dB p : typ_conv T" using wt by (rule typ_pres)
    hence "termip beta (proc_to_dB p)" by (rule type_implies_termi)
    hence "termip beta2 p" unfolding beta2_def by (rule termip_map)
    with termip_leq show ?thesis by auto
  qed
qed

inductive par_beta :: "['a procedure, 'a procedure] \<Rightarrow> bool" (infixl "\<Rightarrow>>" 50)
  where
  pb_Proc[simp, intro!]: "proc_relation par_beta s s' ==> Proc s \<Rightarrow>> Proc s'"
| pb_ProcRef [simp, intro!]: "ProcRef n \<Rightarrow>> ProcRef n"
| pb_ProcUnit [simp, intro!]: "ProcUnit \<Rightarrow>> ProcUnit"
| pb_ProcAbs [simp, intro!]: "s \<Rightarrow>> t ==> ProcAbs s \<Rightarrow>> ProcAbs t"
| pb_ProcAppl [simp, intro!]: "[| s \<Rightarrow>> s'; t \<Rightarrow>> t' |] ==> ProcAppl s t \<Rightarrow>> ProcAppl s' t'"
| pb_ProcPair [simp, intro!]: "[| s \<Rightarrow>> s'; t \<Rightarrow>> t' |] ==> ProcPair s t \<Rightarrow>> ProcPair s' t'"
| pb_ProcUnpair [simp, intro!]: "s \<Rightarrow>> t ==> ProcUnpair b s \<Rightarrow>> ProcUnpair b t"
| pb_ProcUnpair1 [simp, intro!]: "s \<Rightarrow>> s' ==> ProcUnpair True (ProcPair s t) \<Rightarrow>> s'"
| pb_ProcUnpair2 [simp, intro!]: "t \<Rightarrow>> t' ==> ProcUnpair False (ProcPair s t) \<Rightarrow>> t'"
| pb_beta [simp, intro!]: "[| s \<Rightarrow>> s'; t \<Rightarrow>> t' |] ==> ProcAppl (ProcAbs s) t \<Rightarrow>> subst_proc 0 t' s'"

inductive_cases par_beta_cases [elim!]:
  "ProcRef n \<Rightarrow>> t"
  "ProcAbs s \<Rightarrow>> ProcAbs t"
  "ProcAppl (ProcAbs s) t \<Rightarrow>> u"
  "ProcAppl s t \<Rightarrow>> u"
  "ProcAbs s \<Rightarrow>> t"
  "Proc b \<Rightarrow>> u"
  "ProcPair p1 p2 \<Rightarrow>> u"
  "ProcUnpair b p \<Rightarrow>> u"
  "ProcUnit \<Rightarrow>> u"

lemma par_beta_varL [simp]:
    "(ProcRef n \<Rightarrow>> t) = (t = ProcRef n)"
  by blast

lemma par_beta_refl [simp]: shows "t \<Rightarrow>> t"  (* par_beta_refl [intro!] causes search to blow up *)
proof (induction n\<equiv>"proc_size t" arbitrary: t rule:nat_less_induct)
  case 1
  hence IH: "x \<Rightarrow>> x" if "proc_size x<proc_size t" for x using that by auto

  show "t \<Rightarrow>> t"
  proof (cases t)
    case (Proc x')
(*     have eq: "z=z'" if "(z, z') \<in> set (zip (proc_list x') (proc_list x'))" for z z'
      by (meson that zip_same) *)
    have size_z: "proc_size z < proc_size t" if "z \<in> set (proc_list x')" for z
      using proc_size_Proc Proc that by simp
(*     have beta: "z\<Rightarrow>>z'" if "(z, z') \<in> set (zip (proc_list x') (proc_list x'))" for z z'
      apply (subst eq, fact that)
      apply (rule IH)
      apply (rule size_z)
      using that
      by (meson in_set_zipE) *)
    show ?thesis
      unfolding Proc apply (rule) unfolding proc_relation_def 
      apply simp
      by (meson "1.hyps" list.rel_refl_strong size_z)
  qed (use 1 in auto)
qed

lemma beta_subset_par_beta: 
  shows "beta_reduce_proc <= par_beta"
proof (rule predicate2I)
  fix x y
  show "beta_reduce_proc x y \<Longrightarrow> x \<Rightarrow>> y"
  proof (induction rule:beta_reduce_proc.induct)
    case (br_Proc i s t)
    hence "proc_relation_nth op \<Rightarrow>> i s t"
      apply (rule predicate2D[where Q="proc_relation_nth op \<Rightarrow>> i", rotated]) 
      apply (rule proc_relation_nth_mono)
      by auto
    hence shape: "same_shape s t" and "i < proc_length s" and upd: "proc_list t = proc_list s[i := proc_list t ! i]" 
      and beta: "proc_list s ! i \<Rightarrow>> proc_list t ! i"
      unfolding proc_relation_nth_def by auto
    from upd have "proc_list s ! i \<Rightarrow>> proc_list t ! i"
      using beta by blast
    moreover from upd have "proc_list s ! n = proc_list t ! n" if "i\<noteq>n" for n using that
      by (metis nth_list_update_neq)
    then have "proc_list s ! n \<Rightarrow>> proc_list t ! n" if "i\<noteq>n" for n
      using par_beta_refl that by auto
    ultimately have "list_all2 op \<Rightarrow>> (proc_list s) (proc_list t)" 
      apply (rule_tac list_all2_all_nthI)
       apply (metis upd length_list_update)
      by (case_tac "n=i", auto)
    with shape have "proc_relation op \<Rightarrow>> s t" unfolding proc_relation_def by auto
    then show ?case by auto
  qed auto
qed


inductive_cases beta_reduce_cases [elim!]:
  "beta_reduce_proc (ProcRef i) t"
  "beta_reduce_proc (ProcAbs r) s"
  "beta_reduce_proc (ProcAppl s t) u"
  "beta_reduce_proc (ProcPair s t) s"
  "beta_reduce_proc (ProcUnpair b t) u"


lemma rtrancl_beta_Proc [intro!]:
  assumes "proc_relation_nth (beta_reduce_proc\<^sup>*\<^sup>*) i s s'"
  shows "beta_reduce_proc\<^sup>*\<^sup>* (Proc s) (Proc s')"
proof -
  from assms
  have shape: "same_shape s s'" and i_s: "i < proc_length s" and upd: "proc_list s' = proc_list s[i := proc_list s' ! i]" 
      and beta: "beta_reduce_proc\<^sup>*\<^sup>* (proc_list s ! i) (proc_list s' ! i)"
    unfolding proc_relation_nth_def by auto
  define si s'i where "si = proc_list s!i" and "s'i = proc_list s'!i"
  have br_proc: "beta_reduce_proc\<^sup>*\<^sup>* (Proc s) (Proc s')"
    using beta unfolding si_def[symmetric] s'i_def[symmetric]
  proof (insert si_def s'i_def upd shape, induction arbitrary: s' rule:rtranclp.induct)
    case (rtrancl_refl a)
    then have "s=s'"
      by (subst same_shape_list[symmetric], simp)
    then show ?case
      by simp
  next
    case (rtrancl_into_rtrancl si ti s'i)
    hence shape_ss': "same_shape s s'" and beta_ti_s'i: "beta_reduce_proc ti s'i" 
      and s'i: "s'i = proc_list s' ! i" and si: "si = proc_list s ! i" 
      and s's: "proc_list s' = proc_list s[i := proc_list s' ! i]" by auto
    define t where "t = proc_update s i ti"
    hence ti: "ti = proc_list t ! i"
      by (simp add: i_s proc_update_list)
    have shape_st: "same_shape s t"
      by (simp add: proc_update_def t_def)
    with shape_ss' have shape_ts': "same_shape t s'"
      using same_shape_sym same_shape_trans by metis
    have i_t: " i < proc_length t" using i_s shape_st
      using modules.proc_update_list modules_axioms t_def by fastforce
    have s't: "proc_list s'  = proc_list t[i := proc_list s' ! i]"
      using proc_update_list rtrancl_into_rtrancl.prems(3) t_def by auto 
    have ts: "proc_list t = proc_list s[i := proc_list t ! i]"
      using s's s't
      using proc_update_list t_def ti by presburger
    have beta_Proc_st: "beta_reduce_proc\<^sup>*\<^sup>* (Proc s) (Proc t)"
      apply (rule rtrancl_into_rtrancl.IH)
      using si ti ts shape_st .
    have "proc_relation_nth beta_reduce_proc i t s'"
      unfolding proc_relation_nth_def 
      using s't shape_st i_t shape_ts' shape_st beta_ti_s'i ti s'i by auto
    hence beta_Proc_ts': "beta_reduce_proc (Proc t) (Proc s')"
      by (rule br_Proc[where i=i])
    from beta_Proc_st beta_Proc_ts' show ?case by rule
  qed

  then show ?thesis by auto
qed


lemma take_drop_nth:
  assumes "i<length xs" and "i<length ys" 
  shows "(take i xs @ drop i ys) ! i = ys ! i"
proof -
  have "length (take i xs) = i"
    using assms(1) by auto
  hence "(take i xs @ drop i ys) ! i = hd (drop i ys)"
    by (metis Cons_nth_drop_Suc assms(2) hd_drop_conv_nth nth_append_length)
  also have "\<dots> = ys ! i"
    apply (rule hd_drop_conv_nth)
    using assms by simp
  finally show ?thesis .
  find_theorems drop nth
qed

lemma take_append': assumes "n\<le>length xs" shows "take n (xs @ ys) = take n xs"
  apply (subst take_append)
  apply (subst diff_is_0_eq') using assms close
  by simp

lemma take_take': assumes "n\<le>m" shows "take n (take m xs) = take n xs"
  apply (subst take_take)
  apply (subst min.absorb1) using assms by auto

lemma drop_append': assumes "n=length xs" shows "drop n (xs @ ys) = ys"
  unfolding drop_append using assms by auto

lemma rtrancl_beta_Proc' [intro!]:
  assumes "proc_relation (beta_reduce_proc\<^sup>*\<^sup>*) s s'"
  shows "beta_reduce_proc\<^sup>*\<^sup>* (Proc s) (Proc s')"
proof -
  define hyb where "hyb i = proc_update' s (take i (proc_list s') @ drop i (proc_list s))" for i
  have shape: "same_shape (hyb i) s" for i
  proof -
    have hybi: "hyb i = proc_update' s (proc_list (hyb i))" 
      unfolding hyb_def
      by (metis proc_update'_self proc_update'_twice)
    have len': "length (take i (proc_list s') @ drop i (proc_list s)) = proc_length s"
      using assms list_all2_lengthD proc_relation_def by fastforce
    have len: "proc_length (hyb i) = proc_length s"
      unfolding hyb_def
      apply (subst proc_update'_list)
      unfolding len' ..
    show ?thesis
      unfolding same_shape_def using hybi len by simp
  qed

  have hybi_list: "proc_list (hyb (Suc i)) = proc_list (hyb i)[i := proc_list (hyb (Suc i)) ! i]" if "i<proc_length s" for i 
  proof -
    from that have is': "i<proc_length s'"       using assms proc_relation_def same_shape_def by auto

    have "proc_list (hyb (Suc i)) = take i (proc_list (hyb (Suc i))) @ proc_list (hyb (Suc i)) ! i # drop (Suc i) (proc_list (hyb (Suc i)))"
      apply (rule id_take_nth_drop[where i=i])
      using same_shape_def shape that by auto
    also have "take i (proc_list (hyb (Suc i))) = take i (proc_list s')"
      apply (subst hyb_def)
      apply (subst proc_update'_list)
      using assms proc_relation_def same_shape_def close
      apply (subst take_append') 
       apply simp
      using assms list_all2_lengthD proc_relation_def that close fastforce
      apply (subst take_take') by auto
    also have hybs_i: "proc_list (hyb (Suc i)) ! i = proc_list s' ! i"
      unfolding hyb_def
      apply (subst proc_update'_list)
      using assms proc_relation_def same_shape_def close
      apply (subst nth_append)
      apply (rewrite at "i<_"  DEADID.rel_mono_strong[of _ True])
      using assms list_all2_lengthD proc_relation_def that close fastforce
      by simp
    also have "drop (Suc i) (proc_list (hyb (Suc i))) = drop (Suc i) (proc_list s)"
      unfolding hyb_def
      apply (subst proc_update'_list)
      using assms proc_relation_def same_shape_def close
       apply (subst drop_append')
      using assms proc_relation_def same_shape_def that by auto
    finally have pl_hybsi: "proc_list (hyb (Suc i)) = take i (proc_list s') @ proc_list s' ! i # drop (Suc i) (proc_list s)" .

    have "proc_list (hyb i) = take i (proc_list s') @ drop i (proc_list s)"
      unfolding hyb_def
      apply (subst proc_update'_list)
      using assms proc_relation_def same_shape_def close
      by auto
    also have "drop i (proc_list s) = proc_list s ! i # drop (Suc i) (proc_list s)"
      apply (subst Cons_nth_drop_Suc)
      using that by auto
    finally have pl_hybi: "proc_list (hyb i) = take i (proc_list s') @ proc_list s ! i # drop (Suc i) (proc_list s)" .

    have "proc_list (hyb i)[i := proc_list (hyb (Suc i)) ! i] = take i (proc_list s') @ proc_list (hyb (Suc i)) ! i # drop (Suc i) (proc_list s)"
      unfolding pl_hybi 
      apply (rewrite at "_[\<hole>:=_]" DEADID.rel_mono_strong[where y="length (take i (proc_list s'))"])
      using is' close
      apply (subst list_update_length) ..
    moreover note hybs_i
    moreover note pl_hybsi[symmetric]
    ultimately show ?thesis by simp
  qed


  have beta_hyb: "beta_reduce_proc\<^sup>*\<^sup>* (proc_list (hyb i) ! i) (proc_list (hyb (Suc i)) ! i)" if "i<proc_length s" for i
  proof -
    from that have is': "i<proc_length s'"       using assms proc_relation_def same_shape_def by auto

    have hybi: "proc_list (hyb i) ! i = proc_list s ! i"
      unfolding hyb_def 
      apply (subst proc_update'_list) using assms list_all2_lengthD proc_relation_def close fastforce
      apply (subst take_drop_nth)
      using is' that by auto

    have hybsi: "(proc_list (hyb (Suc i)) ! i) = proc_list s' ! i"
      unfolding hyb_def
      apply (subst proc_update'_list) using assms list_all2_lengthD proc_relation_def close fastforce
      apply (subst nth_append)
      apply (rewrite at "i<_"  DEADID.rel_mono_strong[of _ True])
      using assms list_all2_lengthD proc_relation_def that close fastforce
      by simp
      
    show ?thesis
      unfolding hybi hybsi
      using assms list_all2_nthD proc_relation_def that by auto
  qed
  have beta_hyb': "beta_reduce_proc\<^sup>*\<^sup>* (Proc (hyb i)) (Proc (hyb (Suc i)))" if " i < proc_length s" for i
    apply (rule rtrancl_beta_Proc[where i=i])
    unfolding proc_relation_nth_def apply auto
    using shape same_shape_trans same_shape_sym close metis
    using that shape same_shape_def close simp
    using that apply (rule hybi_list)
    using that by (rule beta_hyb)

  define ls where "ls = (proc_length s)"
  hence ls': "ls \<le> proc_length s" by simp
  have beta_n: "beta_reduce_proc\<^sup>*\<^sup>* (Proc (hyb 0)) (Proc (hyb ls))"
    apply (insert ls', induction ls)
     close
    apply (rule rtranclp_trans)
     close simp
    apply (rule beta_hyb')
    by auto

  have hyb0: "hyb 0 = s"
    unfolding hyb_def by simp
  have hybn: "hyb (proc_length s) = s'"
    unfolding hyb_def apply simp
    using assms proc_relation_def same_shape_def same_shape_sym by auto

  show ?thesis
    using beta_n unfolding ls_def hyb0 hybn .
qed

lemma rtrancl_beta_ProcAbs [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcAbs s) (ProcAbs s')"
apply (induct set: rtranclp)  apply auto
  by (meson br_ProcAbs rtranclp.simps)

lemma rtrancl_beta_ProcAppl1 [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcAppl s t) (ProcAppl s' t)"
  apply (induct set: rtranclp)  apply auto
  by (meson beta_reduce_proofs.br_ProcAppl1 beta_reduce_proofs_axioms rtranclp.simps)


lemma rtrancl_beta_ProcAppl2 [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* t t' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcAppl s t) (ProcAppl s t')"
  apply (induct set: rtranclp)  apply auto
  by (meson beta_reduce_proofs.beta_reduce_proc.intros(4) beta_reduce_proofs_axioms rtranclp.simps)

lemma rtrancl_beta_ProcPair1 [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcPair s t) (ProcPair s' t)"
  apply (induct set: rtranclp)  apply auto
  by (meson beta_reduce_proofs.br_ProcPair1 beta_reduce_proofs_axioms rtranclp.simps)

lemma rtrancl_beta_ProcPair2 [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* t t' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcPair s t) (ProcPair s t')"
  apply (induct set: rtranclp)  apply auto
  by (meson beta_reduce_proofs.br_ProcPair2 beta_reduce_proofs_axioms rtranclp.simps)


lemma rtrancl_beta_ProcUnpair [intro!]:
  "beta_reduce_proc\<^sup>*\<^sup>* s s' \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* (ProcUnpair b s) (ProcUnpair b s')"
  apply (induct set: rtranclp)  apply auto
  by (meson beta_reduce_proofs.beta_reduce_proc.intros(8) beta_reduce_proofs_axioms rtranclp.simps)






lemma par_beta_subset_beta: shows "par_beta <= beta_reduce_proc^**" 
proof (rule predicate2I)
  fix x y
  show "x \<Rightarrow>> y \<Longrightarrow> beta_reduce_proc\<^sup>*\<^sup>* x y"
  proof (induction rule:par_beta.induct)
    case (pb_Proc s s') 
    hence "proc_relation beta_reduce_proc\<^sup>*\<^sup>* s s'"
      using list_all2_mono proc_relation_def by auto
    then show ?case
      by (rule rtrancl_beta_Proc')
  next case (pb_ProcAbs s t) thus ?case
     by (rule_tac rtrancl_beta_ProcAbs, simp)
  next case (pb_ProcAppl s s' t t') thus ?case
    apply (rule_tac rtranclp_trans[where y="ProcAppl s' t"])
    apply (rule rtrancl_beta_ProcAppl1, simp)
    by (rule rtrancl_beta_ProcAppl2, simp)
  next case (pb_beta s s' t t') thus ?case
    apply (rule_tac rtranclp.rtrancl_into_rtrancl[where b="ProcAppl (ProcAbs s') t'"])
    apply (rule_tac rtranclp_trans[where y="ProcAppl (ProcAbs s) t'"])
    apply (rule rtrancl_beta_ProcAppl2, simp)
    apply (rule rtrancl_beta_ProcAppl1)
    apply (rule rtrancl_beta_ProcAbs, simp)
    using beta_reduce_proc.intros by auto
  next case (pb_ProcPair s s' t t') thus ?case
    apply (rule_tac rtranclp_trans[where y="ProcPair s' t"])
    apply (rule rtrancl_beta_ProcPair1, simp)
    by (rule rtrancl_beta_ProcPair2, simp)
  next case (pb_ProcUnpair s t b) thus ?case
     by (rule_tac rtrancl_beta_ProcUnpair, simp)
  next case (pb_ProcUnpair1 s s' t) thus ?case
    apply (rule_tac Transitive_Closure.converse_rtranclp_into_rtranclp[where b=s], auto)
    using beta_reduce_proc.intros by presburger
  next case (pb_ProcUnpair2 t t' s) thus ?case
    apply (rule_tac Transitive_Closure.converse_rtranclp_into_rtranclp[where b=t], auto)
    using beta_reduce_proc.intros by (metis (full_types))
  qed auto
qed


lemma par_beta_lift [simp]:
  shows "p \<Rightarrow>> p' \<Longrightarrow> lift_proc p n \<Rightarrow>> lift_proc p' n"
proof (induction p arbitrary: p' n) 
  case (Proc p1)
  then show ?case by later
next case (ProcAppl p1 p2) thus ?case by fastforce
next case (ProcPair p1 p2) thus ?case by fastforce
next case (ProcUnpair b p)
  from ProcUnpair.prems show ?case
  proof (erule_tac par_beta_cases)
    fix t assume p':"p' = ProcUnpair b t" and "p \<Rightarrow>> t" 
    with ProcUnpair.IH show "lift_proc (ProcUnpair b p) n \<Rightarrow>> lift_proc p' n" by auto
  next
    fix s t assume b:"b" assume sp':"s \<Rightarrow>> p'" assume p:"p = ProcPair s t"
    have "p \<Rightarrow>> ProcPair p' t"  unfolding p
      using sp' by auto
    with ProcUnpair.IH
    have "lift_proc p n \<Rightarrow>> lift_proc (ProcPair p' t) n" by metis
    also have "lift_proc p n = ProcPair (lift_proc s n) (lift_proc t n)"
      by (metis lift_proc.simps(4) p)
    finally have "lift_proc s n \<Rightarrow>> lift_proc p' n" by auto
    thus "lift_proc (ProcUnpair b p) n \<Rightarrow>> lift_proc p' n" 
      unfolding p using b by auto
  next
    fix s t assume b:"\<not>b" assume sp':"t \<Rightarrow>> p'" assume p:"p = ProcPair s t"
    have "p \<Rightarrow>> ProcPair s p'"  unfolding p
      using sp' by auto
    with ProcUnpair.IH
    have "lift_proc p n \<Rightarrow>> lift_proc (ProcPair s p') n" by metis
    also have "lift_proc p n = ProcPair (lift_proc s n) (lift_proc t n)"
      by (metis lift_proc.simps(4) p)
    finally have "lift_proc t n \<Rightarrow>> lift_proc p' n" by auto
    thus "lift_proc (ProcUnpair b p) n \<Rightarrow>> lift_proc p' n" 
      unfolding p using b by auto
  qed
qed auto

lemma par_beta_subst:
  shows "s \<Rightarrow>> s' \<Longrightarrow> t \<Rightarrow>> t' \<Longrightarrow> subst_proc n s t \<Rightarrow>> subst_proc n s' t'"
proof (induction t arbitrary: s s' t' n)
next case Proc thus ?case by auto
next case ProcRef thus ?case by auto
next case ProcUnit thus ?case by auto
next case ProcAbs thus ?case by auto
next case (ProcAppl p q) 
  have "ProcAppl p q \<Rightarrow>> t'" by (fact ProcAppl)
  hence cases: "\<And>P. (\<And>p' p'' q'. \<lbrakk> t' = subst_proc 0 q' p'; p = ProcAbs p''; p'' \<Rightarrow>> p'; q \<Rightarrow>> q' \<rbrakk> \<Longrightarrow> P) \<Longrightarrow>
                    (\<And>p' q'. \<lbrakk> t' = ProcAppl p' q'; p \<Rightarrow>> p'; q \<Rightarrow>> q' \<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P"
    by auto
  show ?case
  proof (rule cases)
    fix p' q' p''
    assume t': "t' = subst_proc 0 q' p'" and p:"p = ProcAbs p''" and p': "p'' \<Rightarrow>> p'" and q': "q \<Rightarrow>> q'"
    have l1: "subst_proc n s' t' = subst_proc 0 (subst_proc n s' q') (subst_proc (Suc n) (lift_proc s' 0) p')"
      unfolding t'
      by (simp add: Procedures.subst_subst(2))
    have "ProcAbs (subst_proc (Suc n) (lift_proc s 0) p'') \<Rightarrow>> ProcAbs (subst_proc (Suc n) (lift_proc s' 0) p')"
      apply (subst subst_proc_ProcAbs[symmetric])+ 
      apply (rule ProcAppl.hyps[unfolded p]) 
       close (fact ProcAppl.prems)
      by (simp add: p')
    hence l2: "subst_proc (Suc n) (lift_proc s 0) p'' \<Rightarrow>> subst_proc (Suc n) (lift_proc s' 0) p'" by blast
    show "subst_proc n s (ProcAppl p q) \<Rightarrow>> subst_proc n s' t'"
      unfolding l1 p apply (subst subst_proc_ProcAppl) apply (subst subst_proc_ProcAbs)
      apply (rule pb_beta)
       close (fact l2)
      using ProcAppl.prems(1) q' by (rule ProcAppl.hyps)
  next
    fix p' q' assume t': "t' = ProcAppl p' q'" and p': "p \<Rightarrow>> p'" and q': "q \<Rightarrow>> q'"
    show "subst_proc n s (ProcAppl p q) \<Rightarrow>> subst_proc n s' t' "
      by (simp add: ProcAppl.hyps(1) ProcAppl.hyps(2) ProcAppl.prems(1) p' q' t')
  qed
next case (ProcUnpair b t) 
  from ProcUnpair.prems show ?case
  proof (erule_tac par_beta_cases)
    fix t0 assume "s \<Rightarrow>> s'" and "t' = ProcUnpair b t0" and "t \<Rightarrow>> t0"
    thus "subst_proc n s (ProcUnpair b t) \<Rightarrow>> subst_proc n s' t'"
      by (metis (poly_guards_query) ProcUnpair.hyps Procedures.subst_proc_ProcUnpair beta_reduce_proofs.pb_ProcUnpair)
  next
    fix s0 t0 assume ss': "s \<Rightarrow>> s'" assume s0t': "s0 \<Rightarrow>> t'"
    assume b:"b" assume t:"t = ProcPair s0 t0"
    from t s0t' have "t \<Rightarrow>> ProcPair t' t0" by auto
    with ss' have "subst_proc n s (ProcPair s0 t0) \<Rightarrow>> subst_proc n s' (ProcPair t' t0)" 
      unfolding t[symmetric] by (rule_tac ProcUnpair.hyps, auto)
    hence "subst_proc n s s0 \<Rightarrow>> subst_proc n s' t'" by auto
    thus "subst_proc n s (ProcUnpair b t) \<Rightarrow>> subst_proc n s' t'"
      by (auto simp: t b)
  next
    fix s0 t0 assume ss': "s \<Rightarrow>> s'" assume s0t': "t0 \<Rightarrow>> t'"
    assume b:"\<not>b" assume t:"t = ProcPair s0 t0"
    from t s0t' have "t \<Rightarrow>> ProcPair s0 t'" by auto
    with ss' have "subst_proc n s (ProcPair s0 t0) \<Rightarrow>> subst_proc n s' (ProcPair s0 t')" 
      unfolding t[symmetric] by (rule_tac ProcUnpair.hyps, auto)
    hence "subst_proc n s t0 \<Rightarrow>> subst_proc n s' t'" by auto
    thus "subst_proc n s (ProcUnpair b t) \<Rightarrow>> subst_proc n s' t'"
      by (auto simp: t b)
  qed
next case (ProcPair p q) thus ?case
   by (auto simp: subst_subst [symmetric])
qed

subsection {* Confluence (directly) *}

lemma diamond_par_beta: shows "diamond par_beta'" and "diamond par_beta" 
proof -
  {fix x y x' y' 
  have "y' \<rightarrow>> x' \<Longrightarrow> \<forall>z'. y' \<rightarrow>> z' \<longrightarrow> (\<exists>u'. x' \<rightarrow>> u' \<and> z' \<rightarrow>> u')"
  and  "y \<Rightarrow>> x \<Longrightarrow> \<forall>z. y \<Rightarrow>> z \<longrightarrow> (\<exists>u. x \<Rightarrow>> u \<and> z \<Rightarrow>> u)"
    proof (induction y' x' and y x rule:par_beta'_par_beta.inducts)
    case pb_Assign thus ?case by (blast intro!: par_beta_subst)
    next case pb_Sample thus ?case by (blast intro!: par_beta_subst)
    next case pb_Seq thus ?case by (blast intro!: par_beta_subst)
    next case pb_Skip thus ?case by (blast intro!: par_beta_subst)
    next case pb_IfTE thus ?case by (blast intro!: par_beta_subst)
    next case pb_While thus ?case by (blast intro!: par_beta_subst)
    next case pb_CallProc thus ?case by (blast intro!: par_beta_subst)
    next case pb_Proc thus ?case by (blast intro!: par_beta_subst)
    next case pb_ProcRef thus ?case by (blast intro!: par_beta_subst)
    next case pb_ProcUnit thus ?case by auto
    next case pb_ProcAbs thus ?case by auto
    next case pb_ProcAppl thus ?case  by (blast intro!: par_beta_subst)
    next case pb_ProcPair thus ?case by (blast intro!: par_beta_subst)
    next case pb_beta thus ?case by (blast intro!: par_beta_subst)
    next case pb_ProcUnpair1 thus ?case by (blast intro!: par_beta_subst)
    next case pb_ProcUnpair2 thus ?case by (blast intro!: par_beta_subst)
    next case (pb_ProcUnpair s t b) show ?case 
      proof auto
        fix ta assume "s \<Rightarrow>> ta" 
        thus "\<exists>u. ProcUnpair b t \<Rightarrow>> u \<and> ProcUnpair b ta \<Rightarrow>> u"
          by (metis (full_types) beta_reduce_proofs.pb_ProcUnpair pb_ProcUnpair.IH)
      next
        fix z sa ta assume saz:"sa \<Rightarrow>> z" assume b assume s:"s = ProcPair sa ta" 
        thm pb_ProcUnpair.IH
        obtain u where tu:"t \<Rightarrow>> u" and ztau:"ProcPair z ta \<Rightarrow>> u"
          by (metis saz beta_reduce_proofs.par_beta_refl(2) beta_reduce_proofs.pb_ProcPair pb_ProcUnpair.IH s)
        obtain u1 u2 where u:"u=ProcPair u1 u2" and zu1:"z\<Rightarrow>>u1"
          by (metis ztau beta_reduce_proofs.par_beta_cases(14))
        obtain sa0 ta0 where t:"t = ProcPair sa0 ta0"
          by (metis s beta_reduce_proofs.par_beta_cases(14) pb_ProcUnpair.hyps)
        from tu have sa0u1: "sa0 \<Rightarrow>> u1" unfolding t u by (cases, auto)
        show "\<exists>u. ProcUnpair True t \<Rightarrow>> u \<and> z \<Rightarrow>> u"
          apply (rule exI[of _ u1])
          unfolding t using sa0u1 zu1 by auto
      next
        fix z sa ta assume taz:"ta \<Rightarrow>> z" assume "\<not>b" assume s:"s = ProcPair sa ta" 
        thm pb_ProcUnpair.IH
        obtain u where tu:"t \<Rightarrow>> u" and ztau:"ProcPair sa z \<Rightarrow>> u"
          by (metis taz beta_reduce_proofs.par_beta_refl(2) beta_reduce_proofs.pb_ProcPair pb_ProcUnpair.IH s)
        obtain u1 u2 where u:"u=ProcPair u1 u2" and zu2:"z\<Rightarrow>>u2"
          by (metis ztau beta_reduce_proofs.par_beta_cases(14))
        obtain sa0 ta0 where t:"t = ProcPair sa0 ta0"
          by (metis s beta_reduce_proofs.par_beta_cases(14) pb_ProcUnpair.hyps)
        from tu have ta0u2: "ta0 \<Rightarrow>> u2" unfolding t u by (cases, auto)
        show "\<exists>u. ProcUnpair False t \<Rightarrow>> u \<and> z \<Rightarrow>> u"
          apply (rule exI[of _ u2])
          unfolding t using ta0u2 zu2 by auto
      qed
    qed}
  thus "diamond par_beta'" and "diamond par_beta"
    unfolding diamond_def commute_def square_def by auto
qed


subsection {* Complete developments *}

fun cd' :: "program_rep \<Rightarrow> program_rep"
and cd :: "procedure_rep \<Rightarrow> procedure_rep" where
  "cd' Skip = Skip"
| "cd' (Assign x e) = Assign x e"
| "cd' (Sample x e) = Sample x e"
| "cd' (Seq p1 p2) = Seq (cd' p1) (cd' p2)"
| "cd' (IfTE c p1 p2) = IfTE c (cd' p1) (cd' p2)"
| "cd' (While c p) = While c (cd' p)"
| "cd' (CallProc v p e) = CallProc v (cd p) e"
| "cd (Proc body args ret) = Proc (cd' body) args ret"
| "cd (ProcRef n) = ProcRef n"
| "cd ProcUnit = ProcUnit"
| "cd (ProcAppl (ProcAppl s1 s2) t) = ProcAppl (cd (ProcAppl s1 s2)) (cd t)"
| "cd (ProcAppl (ProcAbs u) t) = subst_proc 0 (cd t) (cd u)"
| "cd (ProcAppl t u) = ProcAppl (cd t) (cd u)"
| "cd (ProcAbs s) = ProcAbs (cd s)"
| "cd (ProcPair s t) = ProcPair (cd s) (cd t)"
| "cd (ProcUnpair b (ProcPair p1 p2)) = (if b then cd p1 else cd p2)"
| "cd (ProcUnpair b t) = ProcUnpair b (cd t)"

subsection {* Confluence (via complete developments) *}

theorem beta_confluent: "confluent beta_reduce_proc"
  apply (rule diamond_to_confluence)
  close (rule diamond_par_beta)
  close (rule beta_subset_par_beta)
  by (rule par_beta_subset_beta)

theorem beta_prog_confluent: "confluent beta_reduce_prog"
  apply (rule diamond_to_confluence)
  close (rule diamond_par_beta)
  close (rule beta_subset_par_beta)
  by (rule par_beta_subset_beta)


end

