theory ProcStrongNorm
imports Main
begin

text {*
Based on HOL/Proofs/Lambda/StrongNorm, 
a formalization by Stefan Berghofer. 
*}

declare [[syntax_ambiguity_warning = false]]

subsection {* Lambda-terms in de Bruijn notation and substitution *}

(*
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
*)

typedecl tmp

datatype program_rep =
  Skip
| CallProc tmp procedure_rep tmp
and procedure_rep =
    Proc program_rep tmp tmp
  | ProcRef nat
  | ProcAppl procedure_rep procedure_rep (infixl "\<degree>" 200)
  | ProcAbs procedure_rep

type_synonym dB = procedure_rep
abbreviation "Var == ProcRef"
abbreviation "App == ProcAppl"
abbreviation "Abs == ProcAbs"

primrec
  lift' :: "[program_rep, nat] => program_rep" and
  lift :: "[dB, nat] => dB"
where
    "lift (Var i) k = (if i < k then Var i else Var (i + 1))"
  | "lift (s \<degree> t) k = lift s k \<degree> lift t k"
  | "lift (Abs s) k = Abs (lift s (k + 1))"
  | "lift (Proc body a r) k = Proc (lift' body k) a r"
  | "lift' Skip k = Skip"
  | "lift' (CallProc x p y) k = CallProc x (lift p k) y"

primrec
  subst' :: "[program_rep, dB, nat] => program_rep"  ("_[_'/''_]" [300, 0, 0] 300) and
  subst :: "[dB, dB, nat] => dB"  ("_[_'/_]" [300, 0, 0] 300)
where (* FIXME base names *)
    subst_Var: "(Var i)[s/k] =
      (if k < i then Var (i - 1) else if i = k then s else Var i)"
  | subst_App: "(t \<degree> u)[s/k] = t[s/k] \<degree> u[s/k]"
  | subst_Abs: "(Abs t)[s/k] = Abs (t[lift s 0 / k+1])"
  | subst_Proc: "(Proc body x y)[s/k] = Proc (body[s/'k]) x y"
  | subst_Skip: "Skip[s/'k] = Skip"
  | subst_CallProc: "(CallProc x p y)[s/'k] = CallProc x (p[s/k]) y"

declare subst_Var [simp del]

text {* Optimized versions of @{term subst} and @{term lift}. *}

primrec
  liftn' :: "[nat, program_rep, nat] => program_rep" and
  liftn :: "[nat, dB, nat] => dB"
where
    "liftn n (Var i) k = (if i < k then Var i else Var (i + n))"
  | "liftn n (s \<degree> t) k = liftn n s k \<degree> liftn n t k"
  | "liftn n (Abs s) k = Abs (liftn n s (k + 1))"
  | "liftn n (Proc body x y) k = Proc (liftn' n body k) x y"
  | "liftn' n Skip k = Skip"
  | "liftn' n (CallProc x p y) k = CallProc x (liftn n p k) y"


primrec
  substn' :: "[program_rep, dB, nat] => program_rep" and
  substn :: "[dB, dB, nat] => dB"
where
    "substn (Var i) s k =
      (if k < i then Var (i - 1) else if i = k then liftn k s 0 else Var i)"
  | "substn (t \<degree> u) s k = substn t s k \<degree> substn u s k"
  | "substn (Abs t) s k = Abs (substn t s (k + 1))"
  | "substn (Proc p x y) s k = Proc (substn' p s k) x y"
  | "substn' Skip s k = Skip"
  | "substn' (CallProc x p y) s k = CallProc x (substn p s k) y"


subsection {* Beta-reduction *}

inductive 
  beta' :: "[program_rep, program_rep] => bool"  (infixl "\<longrightarrow>\<^sub>\<beta>" 50) and
  beta :: "[dB, dB] => bool"  (infixl "\<rightarrow>\<^sub>\<beta>" 50)
  where
    beta [simp, intro!]: "Abs s \<degree> t \<rightarrow>\<^sub>\<beta> s[t/0]"
  | appL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> s \<degree> u \<rightarrow>\<^sub>\<beta> t \<degree> u"
  | appR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> u \<degree> s \<rightarrow>\<^sub>\<beta> u \<degree> t"
  | abs [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> Abs s \<rightarrow>\<^sub>\<beta> Abs t"
  | [simp, intro!]: "s \<longrightarrow>\<^sub>\<beta> t ==> Proc s x y \<rightarrow>\<^sub>\<beta> Proc t x y"
  | [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> CallProc x s y \<longrightarrow>\<^sub>\<beta> CallProc x t y"
abbreviation
  beta_reds  :: "[dB, dB] => bool"  (infixl "->>" 50) where
  "s ->> t == beta^** s t"
abbreviation
  beta_reds' :: "[program_rep, program_rep] => bool"  (infixl "-->>" 50) where
  "s -->> t == beta'^** s t"

notation (latex)
  beta_reds  (infixl "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50) and
  beta_reds'  (infixl "\<longrightarrow>\<^sub>\<beta>\<^sup>*" 50)

inductive_cases beta_cases [elim!]:
  "Var i \<rightarrow>\<^sub>\<beta> t"
  "Abs r \<rightarrow>\<^sub>\<beta> s"
  "s \<degree> t \<rightarrow>\<^sub>\<beta> u"
  "Proc p x y \<rightarrow>\<^sub>\<beta> u"
  "Skip \<longrightarrow>\<^sub>\<beta> u"

declare if_not_P [simp] not_less_eq [simp]
  -- {* don't add @{text "r_into_rtrancl[intro!]"} *}


subsection {* Congruence rules *}

lemma rtrancl_beta_Abs [intro!]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' ==> Abs s \<rightarrow>\<^sub>\<beta>\<^sup>* Abs s'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_Proc [intro!]:
    "s \<longrightarrow>\<^sub>\<beta>\<^sup>* s' ==> Proc s x y \<rightarrow>\<^sub>\<beta>\<^sup>* Proc s' x y"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_CallProc [intro!]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' ==> CallProc x s y \<longrightarrow>\<^sub>\<beta>\<^sup>* CallProc x s' y"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppL:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' ==> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<degree> t"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_AppR:
    "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' ==> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s \<degree> t'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_App [intro]:
    "[| s \<rightarrow>\<^sub>\<beta>\<^sup>* s'; t \<rightarrow>\<^sub>\<beta>\<^sup>* t' |] ==> s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<degree> t'"
  by (blast intro!: rtrancl_beta_AppL rtrancl_beta_AppR intro: rtranclp_trans)


subsection {* Substitution-lemmas *}

lemma subst_eq [simp]: "(Var k)[u/k] = u"
  by (simp add: subst_Var)

lemma subst_gt [simp]: "i < j ==> (Var j)[u/i] = Var (j - 1)"
  by (simp add: subst_Var)

lemma subst_lt [simp]: "j < i ==> (Var j)[u/i] = Var j"
  by (simp add: subst_Var)

lemma lift_lift:
  shows "i < k + 1 \<Longrightarrow> lift' (lift' p i) (Suc k) = lift' (lift' p k) i"
  and  "i < k + 1 \<Longrightarrow> lift (lift t i) (Suc k) = lift (lift t k) i" 
  by (induct p and t arbitrary: i k and i k) auto

lemma lift_subst [simp]:
  shows "j < i + 1 \<Longrightarrow> lift' (p[s/'j]) i = (lift' p (i + 1)) [lift s i /' j]"
  and "j < i + 1 \<Longrightarrow> lift (t[s/j]) i = (lift t (i + 1)) [lift s i / j]"
  by (induct p and t arbitrary: i j s and i j s)
    (simp_all add: diff_Suc subst_Var lift_lift split: nat.split)

lemma lift_subst_lt:
  shows "i < j + 1 \<Longrightarrow> lift' (p[s/'j]) i = (lift' p i) [lift s i /' j + 1]"
  and "i < j + 1 \<Longrightarrow> lift (t[s/j]) i = (lift t i) [lift s i / j + 1]"
  by (induct p and t arbitrary: i j s and i j s) (simp_all add: subst_Var lift_lift)

lemma subst_lift [simp]:
  shows "(lift' p k)[s/'k] = p"
   and  "(lift t k)[s/k] = t"
  by (induct p and t arbitrary: k s and k s) simp_all

lemma subst_subst:
  shows "i < j + 1 \<Longrightarrow> p[lift v i /' Suc j][u[v/j]/'i] = p[u/'i][v/'j]"
  and   "i < j + 1 \<Longrightarrow> t[lift v i / Suc j][u[v/j]/i] = t[u/i][v/j]"
  by (induct p and t arbitrary: i j u v and i j u v)
    (simp_all add: diff_Suc subst_Var lift_lift [symmetric] lift_subst_lt
      split: nat.split)


subsection {* Equivalence proof for optimized substitution *}

lemma liftn_0 [simp]: shows "liftn' 0 p k = p" and "liftn 0 t k = t"
  by (induct p and t arbitrary: k and k) (simp_all add: subst_Var)

lemma liftn_lift [simp]: 
  shows "liftn' (Suc n) p k = lift' (liftn' n p k) k"
  and   "liftn (Suc n) t k = lift (liftn n t k) k"
  by (induct p and t arbitrary: k and k) (simp_all add: subst_Var)

lemma substn_subst_n [simp]:
  shows "substn' p s n = p[liftn n s 0 /' n]"
  and   "substn t s n = t[liftn n s 0 / n]"
  by (induct p and t arbitrary: n and n) (simp_all add: subst_Var)

theorem substn_subst_0: 
  shows "substn' p s 0 = p[s/'0]"
  and   "substn t s 0 = t[s/0]"
  by simp_all


subsection {* Preservation theorems *}

text {* Not used in Church-Rosser proof, but in Strong
  Normalization. \medskip *}

theorem subst_preserves_beta [simp]:
  shows "pr \<longrightarrow>\<^sub>\<beta> ps ==> pr[t/'i] \<longrightarrow>\<^sub>\<beta> ps[t/'i]"
  and   "r \<rightarrow>\<^sub>\<beta> s ==> r[t/i] \<rightarrow>\<^sub>\<beta> s[t/i]"
  by (induct arbitrary: t i and t i rule:beta'_beta.inducts) (simp_all add: subst_subst [symmetric])

theorem subst_preserves_beta': "r \<rightarrow>\<^sub>\<beta>\<^sup>* s ==> r[t/i] \<rightarrow>\<^sub>\<beta>\<^sup>* s[t/i]"
  apply (induct set: rtranclp)
   apply (rule rtranclp.rtrancl_refl)
  apply (erule rtranclp.rtrancl_into_rtrancl)
  apply (erule subst_preserves_beta)
  done

theorem lift_preserves_beta [simp]:
  shows "pr \<longrightarrow>\<^sub>\<beta> ps ==> lift' pr i \<longrightarrow>\<^sub>\<beta> lift' ps i"
  and   "r \<rightarrow>\<^sub>\<beta> s ==> lift r i \<rightarrow>\<^sub>\<beta> lift s i"
  by (induct arbitrary: i and i rule:beta'_beta.inducts) auto

theorem lift_preserves_beta': "r \<rightarrow>\<^sub>\<beta>\<^sup>* s ==> lift r i \<rightarrow>\<^sub>\<beta>\<^sup>* lift s i"
  apply (induct set: rtranclp)
   apply (rule rtranclp.rtrancl_refl)
  apply (erule rtranclp.rtrancl_into_rtrancl)
  apply (erule lift_preserves_beta)
  done

theorem subst_preserves_beta2 [simp]: 
  shows "r \<rightarrow>\<^sub>\<beta> s ==> p[r/'i] \<longrightarrow>\<^sub>\<beta>\<^sup>* p[s/'i]"
    and "r \<rightarrow>\<^sub>\<beta> s ==> t[r/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t[s/i]"
  apply (induct p and t arbitrary: r s i and r s i)
  apply simp
  apply (simp add: rtrancl_beta_CallProc)
  apply (simp add: rtrancl_beta_Proc)
  apply (simp add: subst_Var r_into_rtranclp)
  apply (simp add: rtrancl_beta_App)
  by (simp add: rtrancl_beta_Abs)
  

theorem subst_preserves_beta2': "r \<rightarrow>\<^sub>\<beta>\<^sup>* s ==> t[r/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t[s/i]"
  apply (induct set: rtranclp)
   apply (rule rtranclp.rtrancl_refl)
  apply (erule rtranclp_trans)
  apply (erule subst_preserves_beta2)
  done

abbreviation
  list_application :: "dB => dB list => dB"  (infixl "\<degree>\<degree>" 150) where
  "t \<degree>\<degree> ts == foldl (op \<degree>) t ts"

lemma apps_eq_tail_conv [iff]: "(r \<degree>\<degree> ts = s \<degree>\<degree> ts) = (r = s)"
  by (induct ts rule: rev_induct) auto

lemma Var_eq_apps_conv [iff]: "(Var m = s \<degree>\<degree> ss) = (Var m = s \<and> ss = [])"
  by (induct ss arbitrary: s) auto

lemma Proc_eq_apps_conv [iff]: "(Proc p x y = s \<degree>\<degree> ss) = (Proc p x y = s \<and> ss = [])"
  by (induct ss arbitrary: s) auto

lemma Var_apps_eq_Var_apps_conv [iff]:
    "(Var m \<degree>\<degree> rs = Var n \<degree>\<degree> ss) = (m = n \<and> rs = ss)"
  apply (induct rs arbitrary: ss rule: rev_induct)
   apply simp
   apply blast
  apply (induct_tac ss rule: rev_induct)
   apply auto
  done

lemma Proc_apps_eq_Proc_apps_conv [iff]:
    "(Proc p x y \<degree>\<degree> rs = Proc p' x' y' \<degree>\<degree> ss) = (p=p' \<and> x=x' \<and> y=y' \<and> rs = ss)"
  apply (induct rs arbitrary: ss rule: rev_induct)
   apply simp
   apply blast
  apply (induct_tac ss rule: rev_induct)
   apply auto
  done

lemma App_eq_foldl_conv:
  "(r \<degree> s = t \<degree>\<degree> ts) =
    (if ts = [] then r \<degree> s = t
    else (\<exists>ss. ts = ss @ [s] \<and> r = t \<degree>\<degree> ss))"
  apply (rule_tac xs = ts in rev_exhaust)
   apply auto
  done

lemma Abs_eq_apps_conv [iff]:
    "(Abs r = s \<degree>\<degree> ss) = (Abs r = s \<and> ss = [])"
  by (induct ss rule: rev_induct) auto

lemma apps_eq_Abs_conv [iff]: "(s \<degree>\<degree> ss = Abs r) = (s = Abs r \<and> ss = [])"
  by (induct ss rule: rev_induct) auto

lemma Abs_apps_eq_Abs_apps_conv [iff]:
    "(Abs r \<degree>\<degree> rs = Abs s \<degree>\<degree> ss) = (r = s \<and> rs = ss)"
  apply (induct rs arbitrary: ss rule: rev_induct)
   apply simp
   apply blast
  apply (induct_tac ss rule: rev_induct)
   apply auto
  done

lemma Abs_App_neq_Var_apps [iff]:
    "Abs s \<degree> t \<noteq> Var n \<degree>\<degree> ss"
  by (induct ss arbitrary: s t rule: rev_induct) auto

lemma Abs_App_neq_Proc_apps [iff]:
    "Abs s \<degree> t \<noteq> Proc p x y \<degree>\<degree> ss"
  by (induct ss arbitrary: s t rule: rev_induct) auto

lemma Var_apps_neq_Abs_apps [iff]:
    "Var n \<degree>\<degree> ts \<noteq> Abs r \<degree>\<degree> ss"
  apply (induct ss arbitrary: ts rule: rev_induct)
   apply simp
  apply (induct_tac ts rule: rev_induct)
   apply auto
  done

lemma Proc_apps_neq_Abs_apps [iff]:
    "Proc p x y \<degree>\<degree> ts \<noteq> Abs r \<degree>\<degree> ss"
  apply (induct ss arbitrary: ts rule: rev_induct)
   apply simp
  apply (induct_tac ts rule: rev_induct)
   apply auto
  done

lemma Var_apps_neq_Proc_apps [iff]:
    "Var n \<degree>\<degree> ts \<noteq> Proc p x y \<degree>\<degree> ss"
  apply (induct ss arbitrary: ts rule: rev_induct)
  apply (induct_tac ts rule: rev_induct, simp_all)
  by (induct_tac ts rule: rev_induct, simp_all)


lemma ex_head_tail:
  "\<exists>ts h. t = h \<degree>\<degree> ts \<and> ((\<exists>n. h = Var n) \<or> (\<exists>u. h = Abs u) \<or> (\<exists>p x y. h=Proc p x y))"
  apply (induct t)
    apply simp
    apply simp
    apply (rule_tac x = "[]" in exI)
    apply simp apply simp
    apply (metis foldl_Cons foldl_Nil foldl_append)
   by simp 

lemma size_apps [simp]:
  "size (r \<degree>\<degree> rs) = size r + foldl (op +) 0 (map size rs) + length rs"
  by (induct rs rule: rev_induct) auto

lemma lem0: "[| (0::nat) < k; m <= n |] ==> m < n + k"
  by simp

lemma lift_map [simp]:
    "lift (t \<degree>\<degree> ts) i = lift t i \<degree>\<degree> map (\<lambda>t. lift t i) ts"
  by (induct ts arbitrary: t) simp_all

lemma subst_map [simp]:
    "subst (t \<degree>\<degree> ts) u i = subst t u i \<degree>\<degree> map (\<lambda>t. subst t u i) ts"
  by (induct ts arbitrary: t) simp_all

lemma app_last: "(t \<degree>\<degree> ts) \<degree> u = t \<degree>\<degree> (ts @ [u])"
  by simp


text {* \medskip A customized induction schema for @{text "\<degree>\<degree>"}. *}

(*
lemma lem:
  assumes "!!n ts. \<forall>t \<in> set ts. P t ==> P (Var n \<degree>\<degree> ts)"
    and "!!u ts. [| P u; \<forall>t \<in> set ts. P t |] ==> P (Abs u \<degree>\<degree> ts)"
  shows "size t = n \<Longrightarrow> P t"
  apply (induct n arbitrary: t rule: nat_less_induct)
  apply (cut_tac t = t in ex_head_tail)
  apply clarify
  apply (erule disjE)
   apply clarify
   apply (rule assms)
   apply clarify
   apply (erule allE, erule impE)
    prefer 2
    apply (erule allE, erule mp, rule refl)
   apply simp
   apply (simp only: foldl_conv_fold add.commute fold_plus_listsum_rev)
   apply (fastforce simp add: listsum_map_remove1)
  apply clarify
  apply (rule assms)
   apply (erule allE, erule impE)
    prefer 2
    apply (erule allE, erule mp, rule refl)
   apply simp
  apply clarify
  apply (erule allE, erule impE)
   prefer 2
   apply (erule allE, erule mp, rule refl)
  apply simp
  apply (rule le_imp_less_Suc)
  apply (rule trans_le_add1)
  apply (rule trans_le_add2)
  apply (simp only: foldl_conv_fold add.commute fold_plus_listsum_rev)
  apply (simp add: member_le_listsum_nat)
  done

theorem Apps_dB_induct:
  assumes "!!n ts. \<forall>t \<in> set ts. P t ==> P (Var n \<degree>\<degree> ts)"
    and "!!u ts. [| P u; \<forall>t \<in> set ts. P t |] ==> P (Abs u \<degree>\<degree> ts)"
  shows "P t"
  apply (rule_tac t = t in lem)
    prefer 3
    apply (rule refl)
    using assms apply iprover+
  done
*)


subsection {* Environments *}

definition
  shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_<_:_>" [90, 0, 0] 91) where
  "e<i:a> = (\<lambda>j. if j < i then e j else if j = i then a else e (j - 1))"

notation (xsymbols)
  shift  ("_\<langle>_:_\<rangle>" [90, 0, 0] 91)

notation (HTML output)
  shift  ("_\<langle>_:_\<rangle>" [90, 0, 0] 91)

lemma shift_eq [simp]: "i = j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = T"
  by (simp add: shift_def)

lemma shift_gt [simp]: "j < i \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e j"
  by (simp add: shift_def)

lemma shift_lt [simp]: "i < j \<Longrightarrow> (e\<langle>i:T\<rangle>) j = e (j - 1)"
  by (simp add: shift_def)

lemma shift_commute [simp]: "e\<langle>i:U\<rangle>\<langle>0:T\<rangle> = e\<langle>0:T\<rangle>\<langle>Suc i:U\<rangle>"
  by (rule ext) (simp_all add: shift_def split: nat.split)


subsection {* Types and typing rules *}

datatype type =
    Atom nat
  | Fun type type    (infixr "\<Rightarrow>" 200)

inductive typing :: "(nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile> _ : _" [50, 50, 50] 50)
  where
    Var [intro!]: "env x = T \<Longrightarrow> env \<turnstile> Var x : T"
  | Abs [intro!]: "env\<langle>0:T\<rangle> \<turnstile> t : U \<Longrightarrow> env \<turnstile> Abs t : (T \<Rightarrow> U)"
  | App [intro!]: "env \<turnstile> s : T \<Rightarrow> U \<Longrightarrow> env \<turnstile> t : T \<Longrightarrow> env \<turnstile> (s \<degree> t) : U"

inductive_cases typing_elims [elim!]:
  "e \<turnstile> Var i : T"
  "e \<turnstile> t \<degree> u : T"
  "e \<turnstile> Abs t : T"

primrec
  typings :: "(nat \<Rightarrow> type) \<Rightarrow> dB list \<Rightarrow> type list \<Rightarrow> bool"
where
    "typings e [] Ts = (Ts = [])"
  | "typings e (t # ts) Ts =
      (case Ts of
        [] \<Rightarrow> False
      | T # Ts \<Rightarrow> e \<turnstile> t : T \<and> typings e ts Ts)"

abbreviation
  typings_rel :: "(nat \<Rightarrow> type) \<Rightarrow> dB list \<Rightarrow> type list \<Rightarrow> bool"
    ("_ ||- _ : _" [50, 50, 50] 50) where
  "env ||- ts : Ts == typings env ts Ts"

notation (latex)
  typings_rel  ("_ \<tturnstile> _ : _" [50, 50, 50] 50)

abbreviation
  funs :: "type list \<Rightarrow> type \<Rightarrow> type"  (infixr "=>>" 200) where
  "Ts =>> T == foldr Fun Ts T"

notation (latex)
  funs  (infixr "\<Rrightarrow>" 200)


subsection {* Some examples *}

schematic_lemma "e \<turnstile> Abs (Abs (Abs (Var 1 \<degree> (Var 2 \<degree> Var 1 \<degree> Var 0)))) : ?T"
  by force

schematic_lemma "e \<turnstile> Abs (Abs (Abs (Var 2 \<degree> Var 0 \<degree> (Var 1 \<degree> Var 0)))) : ?T"
  by force


subsection {* Lists of types *}

lemma lists_typings:
    "e \<tturnstile> ts : Ts \<Longrightarrow> listsp (\<lambda>t. \<exists>T. e \<turnstile> t : T) ts"
  apply (induct ts arbitrary: Ts)
   apply (case_tac Ts)
     apply simp
     apply (rule listsp.Nil)
    apply simp
  apply (case_tac Ts)
   apply simp
  apply simp
  apply (rule listsp.Cons)
   apply blast
  apply blast
  done

lemma types_snoc: "e \<tturnstile> ts : Ts \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<tturnstile> ts @ [t] : Ts @ [T]"
  apply (induct ts arbitrary: Ts)
  apply simp
  apply (case_tac Ts)
  apply simp+
  done

lemma types_snoc_eq: "e \<tturnstile> ts @ [t] : Ts @ [T] =
  (e \<tturnstile> ts : Ts \<and> e \<turnstile> t : T)"
  apply (induct ts arbitrary: Ts)
  apply (case_tac Ts)
  apply simp+
  apply (case_tac Ts)
  apply (case_tac "ts @ [t]")
  apply simp+
  done

lemma rev_exhaust2 [extraction_expand]:
  obtains (Nil) "xs = []"  |  (snoc) ys y where "xs = ys @ [y]"
  -- {* Cannot use @{text rev_exhaust} from the @{text List}
    theory, since it is not constructive *}
  apply (subgoal_tac "\<forall>ys. xs = rev ys \<longrightarrow> thesis")
  apply (erule_tac x="rev xs" in allE)
  apply simp
  apply (rule allI)
  apply (rule impI)
  apply (case_tac ys)
  apply simp
  apply simp
  done

lemma types_snocE: "e \<tturnstile> ts @ [t] : Ts \<Longrightarrow>
  (\<And>Us U. Ts = Us @ [U] \<Longrightarrow> e \<tturnstile> ts : Us \<Longrightarrow> e \<turnstile> t : U \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases Ts rule: rev_exhaust2)
  apply simp
  apply (case_tac "ts @ [t]")
  apply (simp add: types_snoc_eq)+
  done


subsection {* n-ary function types *}

lemma list_app_typeD:
    "e \<turnstile> t \<degree>\<degree> ts : T \<Longrightarrow> \<exists>Ts. e \<turnstile> t : Ts \<Rrightarrow> T \<and> e \<tturnstile> ts : Ts"
  apply (induct ts arbitrary: t T)
   apply simp
  apply (rename_tac a b t T)
  apply atomize
  apply simp
  apply (erule_tac x = "t \<degree> a" in allE)
  apply (erule_tac x = T in allE)
  apply (erule impE)
   apply assumption
  apply (elim exE conjE)
  apply (ind_cases "e \<turnstile> t \<degree> u : T" for t u T)
  apply (rule_tac x = "Ta # Ts" in exI)
  apply simp
  done

lemma list_app_typeE:
  "e \<turnstile> t \<degree>\<degree> ts : T \<Longrightarrow> (\<And>Ts. e \<turnstile> t : Ts \<Rrightarrow> T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow> C) \<Longrightarrow> C"
  by (insert list_app_typeD) fast

lemma list_app_typeI:
    "e \<turnstile> t : Ts \<Rrightarrow> T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow> e \<turnstile> t \<degree>\<degree> ts : T"
  apply (induct ts arbitrary: t T Ts)
   apply simp
  apply (rename_tac a b t T Ts)
  apply atomize
  apply (case_tac Ts)
   apply simp
  apply simp
  apply (erule_tac x = "t \<degree> a" in allE)
  apply (erule_tac x = T in allE)
  apply (rename_tac list)
  apply (erule_tac x = list in allE)
  apply (erule impE)
   apply (erule conjE)
   apply (erule typing.App)
   apply assumption
  apply blast
  done

text {*
For the specific case where the head of the term is a variable,
the following theorems allow to infer the types of the arguments
without analyzing the typing derivation. This is crucial
for program extraction.
*}

theorem var_app_type_eq:
  "e \<turnstile> Var i \<degree>\<degree> ts : T \<Longrightarrow> e \<turnstile> Var i \<degree>\<degree> ts : U \<Longrightarrow> T = U"
  apply (induct ts arbitrary: T U rule: rev_induct)
  apply simp
  apply (ind_cases "e \<turnstile> Var i : T" for T)
  apply (ind_cases "e \<turnstile> Var i : T" for T)
  apply simp
  apply simp
  apply (ind_cases "e \<turnstile> t \<degree> u : T" for t u T)
  apply (ind_cases "e \<turnstile> t \<degree> u : T" for t u T)
  apply atomize
  apply (erule_tac x="Ta \<Rightarrow> T" in allE)
  apply (erule_tac x="Tb \<Rightarrow> U" in allE)
  apply (erule impE)
  apply assumption
  apply (erule impE)
  apply assumption
  apply simp
  done

lemma var_app_types: "e \<turnstile> Var i \<degree>\<degree> ts \<degree>\<degree> us : T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow>
  e \<turnstile> Var i \<degree>\<degree> ts : U \<Longrightarrow> \<exists>Us. U = Us \<Rrightarrow> T \<and> e \<tturnstile> us : Us"
  apply (induct us arbitrary: ts Ts U)
  apply simp
  apply (erule var_app_type_eq)
  apply assumption
  apply simp
  apply (rename_tac a b ts Ts U)
  apply atomize
  apply (case_tac U)
  apply (rule FalseE)
  apply simp
  apply (erule list_app_typeE)
  apply (ind_cases "e \<turnstile> t \<degree> u : T" for t u T)
  apply (drule_tac T="Atom nat" and U="Ta \<Rightarrow> Tsa \<Rrightarrow> T" in var_app_type_eq)
  apply assumption
  apply simp
  apply (erule_tac x="ts @ [a]" in allE)
  apply (erule_tac x="Ts @ [type1]" in allE)
  apply (erule_tac x="type2" in allE)
  apply simp
  apply (erule impE)
  apply (rule types_snoc)
  apply assumption
  apply (erule list_app_typeE)
  apply (ind_cases "e \<turnstile> t \<degree> u : T" for t u T)
  apply (drule_tac T="type1 \<Rightarrow> type2" and U="Ta \<Rightarrow> Tsa \<Rrightarrow> T" in var_app_type_eq)
  apply assumption
  apply simp
  apply (erule impE)
  apply (rule typing.App)
  apply assumption
  apply (erule list_app_typeE)
  apply (ind_cases "e \<turnstile> t \<degree> u : T" for t u T)
  apply (frule_tac T="type1 \<Rightarrow> type2" and U="Ta \<Rightarrow> Tsa \<Rrightarrow> T" in var_app_type_eq)
  apply assumption
  apply simp
  apply (erule exE)
  apply (rule_tac x="type1 # Us" in exI)
  apply simp
  apply (erule list_app_typeE)
  apply (ind_cases "e \<turnstile> t \<degree> u : T" for t u T)
  apply (frule_tac T="type1 \<Rightarrow> Us \<Rrightarrow> T" and U="Ta \<Rightarrow> Tsa \<Rrightarrow> T" in var_app_type_eq)
  apply assumption
  apply simp
  done

lemma var_app_typesE: "e \<turnstile> Var i \<degree>\<degree> ts : T \<Longrightarrow>
  (\<And>Ts. e \<turnstile> Var i : Ts \<Rrightarrow> T \<Longrightarrow> e \<tturnstile> ts : Ts \<Longrightarrow> P) \<Longrightarrow> P"
  apply (drule var_app_types [of _ _ "[]", simplified])
  apply (iprover intro: typing.Var)+
  done

lemma abs_typeE: "e \<turnstile> Abs t : T \<Longrightarrow> (\<And>U V. e\<langle>0:U\<rangle> \<turnstile> t : V \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases T)
  apply (rule FalseE)
  apply (erule typing.cases)
  apply simp_all
  apply atomize
  apply (erule_tac x="type1" in allE)
  apply (erule_tac x="type2" in allE)
  apply (erule mp)
  apply (erule typing.cases)
  apply simp_all
  done


subsection {* Lifting preserves well-typedness *}

lemma lift_type [intro!]: "e \<turnstile> t : T \<Longrightarrow> e\<langle>i:U\<rangle> \<turnstile> lift t i : T"
  by (induct arbitrary: i U set: typing) auto

lemma lift_types:
  "e \<tturnstile> ts : Ts \<Longrightarrow> e\<langle>i:U\<rangle> \<tturnstile> (map (\<lambda>t. lift t i) ts) : Ts"
  apply (induct ts arbitrary: Ts)
   apply simp
  apply (case_tac Ts)
   apply auto
  done


subsection {* Substitution lemmas *}

lemma subst_lemma:
    "e \<turnstile> t : T \<Longrightarrow> e' \<turnstile> u : U \<Longrightarrow> e = e'\<langle>i:U\<rangle> \<Longrightarrow> e' \<turnstile> t[u/i] : T"
  apply (induct arbitrary: e' i U u set: typing)
    apply (rule_tac x = x and y = i in linorder_cases)
      apply auto
  apply blast
  done

lemma substs_lemma:
  "e \<turnstile> u : T \<Longrightarrow> e\<langle>i:T\<rangle> \<tturnstile> ts : Ts \<Longrightarrow>
     e \<tturnstile> (map (\<lambda>t. t[u/i]) ts) : Ts"
  apply (induct ts arbitrary: Ts)
   apply (case_tac Ts)
    apply simp
   apply simp
  apply atomize
  apply (case_tac Ts)
   apply simp
  apply simp
  apply (erule conjE)
  apply (erule (1) subst_lemma)
  apply (rule refl)
  done


subsection {* Subject reduction *}

lemma subject_reduction: "e \<turnstile> t : T \<Longrightarrow> t \<rightarrow>\<^sub>\<beta> t' \<Longrightarrow> e \<turnstile> t' : T"
  apply (induct arbitrary: t' set: typing)
    apply blast
   apply blast
  apply atomize
  apply (ind_cases "s \<degree> t \<rightarrow>\<^sub>\<beta> t'" for s t t')
    apply hypsubst
    apply (ind_cases "env \<turnstile> Abs t : T \<Rightarrow> U" for env t T U)
    apply (rule subst_lemma)
      apply assumption
     apply assumption
    apply (rule ext)
    apply (case_tac x)
     apply auto
  done

theorem subject_reduction': "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> e \<turnstile> t : T \<Longrightarrow> e \<turnstile> t' : T"
  by (induct set: rtranclp) (iprover intro: subject_reduction)+


subsection {* Alternative induction rule for types *}

lemma type_induct [induct type]:
  assumes
  "(\<And>T. (\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> P T1) \<Longrightarrow>
    (\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> P T2) \<Longrightarrow> P T)"
  shows "P T"
proof (induct T)
  case Atom
  show ?case by (rule assms) simp_all
next
  case Fun
  show ?case by (rule assms) (insert Fun, simp_all)
qed


text {*
  Lifting an order to lists of elements, relating exactly one
  element.
*}

definition
  step1 :: "('a => 'a => bool) => 'a list => 'a list => bool" where
  "step1 r =
    (\<lambda>ys xs. \<exists>us z z' vs. xs = us @ z # vs \<and> r z' z \<and> ys =
      us @ z' # vs)"


lemma step1_converse [simp]: "step1 (r^--1) = (step1 r)^--1"
  apply (unfold step1_def)
  apply (blast intro!: order_antisym)
  done

lemma in_step1_converse [iff]: "(step1 (r^--1) x y) = ((step1 r)^--1 x y)"
  apply auto
  done

lemma not_Nil_step1 [iff]: "\<not> step1 r [] xs"
  apply (unfold step1_def)
  apply blast
  done

lemma not_step1_Nil [iff]: "\<not> step1 r xs []"
  apply (unfold step1_def)
  apply blast
  done

lemma Cons_step1_Cons [iff]:
    "(step1 r (y # ys) (x # xs)) =
      (r y x \<and> xs = ys \<or> x = y \<and> step1 r ys xs)"
  apply (unfold step1_def)
  apply (rule iffI)
   apply (erule exE)
   apply (rename_tac ts)
   apply (case_tac ts)
    apply fastforce
   apply force
  apply (erule disjE)
   apply blast
  apply (blast intro: Cons_eq_appendI)
  done

lemma append_step1I:
  "step1 r ys xs \<and> vs = us \<or> ys = xs \<and> step1 r vs us
    ==> step1 r (ys @ vs) (xs @ us)"
  apply (unfold step1_def)
  apply auto
   apply blast
  apply (blast intro: append_eq_appendI)
  done

lemma Cons_step1E [elim!]:
  assumes "step1 r ys (x # xs)"
    and "!!y. ys = y # xs \<Longrightarrow> r y x \<Longrightarrow> R"
    and "!!zs. ys = x # zs \<Longrightarrow> step1 r zs xs \<Longrightarrow> R"
  shows R
  using assms
  apply (cases ys)
   apply (simp add: step1_def)
  apply blast
  done

lemma Snoc_step1_SnocD:
  "step1 r (ys @ [y]) (xs @ [x])
    ==> (step1 r ys xs \<and> y = x \<or> ys = xs \<and> r y x)"
  apply (unfold step1_def)
  apply (clarify del: disjCI)
  apply (rename_tac vs)
  apply (rule_tac xs = vs in rev_exhaust)
   apply force
  apply simp
  apply blast
  done

lemma Cons_acc_step1I [intro!]:
    "Wellfounded.accp r x ==> Wellfounded.accp (step1 r) xs \<Longrightarrow> Wellfounded.accp (step1 r) (x # xs)"
  apply (induct arbitrary: xs set: Wellfounded.accp)
  apply (erule thin_rl)
  apply (erule accp_induct)
  apply (rule accp.accI)
  apply blast
  done

lemma lists_accD: "listsp (Wellfounded.accp r) xs ==> Wellfounded.accp (step1 r) xs"
  apply (induct set: listsp)
   apply (rule accp.accI)
   apply simp
  apply (rule accp.accI)
  apply (fast dest: accp_downward)
  done

lemma ex_step1I:
  "[| x \<in> set xs; r y x |]
    ==> \<exists>ys. step1 r ys xs \<and> y \<in> set ys"
  apply (unfold step1_def)
  apply (drule in_set_conv_decomp [THEN iffD1])
  apply force
  done

lemma lists_accI: "Wellfounded.accp (step1 r) xs ==> listsp (Wellfounded.accp r) xs"
  apply (induct set: Wellfounded.accp)
  apply clarify
  apply (rule accp.accI)
  apply (drule_tac r=r in ex_step1I, assumption)
  apply blast
  done

text {*
  Lifting beta-reduction to lists of terms, reducing exactly one element.
*}

abbreviation
  list_beta :: "dB list => dB list => bool"  (infixl "=>" 50) where
  "rs => ss == step1 beta rs ss"

lemma head_Var_reduction:
  "Var n \<degree>\<degree> rs \<rightarrow>\<^sub>\<beta> v \<Longrightarrow> \<exists>ss. rs => ss \<and> v = Var n \<degree>\<degree> ss"
  apply (induct u == "Var n \<degree>\<degree> rs" v arbitrary: rs set: beta)
     apply simp
    apply (rule_tac xs = rs in rev_exhaust)
     apply simp
    apply (atomize, force intro: append_step1I)
   apply (rule_tac xs = rs in rev_exhaust)
    apply simp
    apply (auto 0 3 intro: disjI2 [THEN append_step1I])
  done

(*
lemma head_Proc_reduction:
  "Proc p x y \<degree>\<degree> rs \<rightarrow>\<^sub>\<beta> v \<Longrightarrow> (\<exists>ss p'. rs => ss \<and> v = Proc p x y \<degree>\<degree> ss)"
  apply (induct u == "Proc p x y \<degree>\<degree> rs" v arbitrary: rs taking: "\<lambda>_ _. True" set: beta)
    apply simp
    apply (rule_tac xs = rs in rev_exhaust)
     apply simp
    apply (atomize, force intro: append_step1I)x
   apply (rule_tac xs = rs in rev_exhaust)
    apply simp
    apply (auto 0 3 intro: disjI2 [THEN append_step1I])[1]
    apply (auto 0 3 intro: disjI2 [THEN append_step1I])[1]
    apply auto[1]
    apply (auto 0 3 intro: disjI2 [THEN append_step1I])[1]
  done
*)

lemma apps_betasE [elim!]:
  assumes major: "r \<degree>\<degree> rs \<rightarrow>\<^sub>\<beta> s"
    and cases: "!!r'. [| r \<rightarrow>\<^sub>\<beta> r'; s = r' \<degree>\<degree> rs |] ==> R"
      "!!rs'. [| rs => rs'; s = r \<degree>\<degree> rs' |] ==> R"
      "!!t u us. [| r = Abs t; rs = u # us; s = t[u/0] \<degree>\<degree> us |] ==> R"
  shows R
proof -
  from major have
   "(\<exists>r'. r \<rightarrow>\<^sub>\<beta> r' \<and> s = r' \<degree>\<degree> rs) \<or>
    (\<exists>rs'. rs => rs' \<and> s = r \<degree>\<degree> rs') \<or>
    (\<exists>t u us. r = Abs t \<and> rs = u # us \<and> s = t[u/0] \<degree>\<degree> us)"
    apply (induct u == "r \<degree>\<degree> rs" s arbitrary: r rs set: beta)
       apply (case_tac r)
         apply simp
         apply simp
        apply (simp add: App_eq_foldl_conv)
        apply (split split_if_asm)
         apply simp
         apply blast
        apply simp
       apply (simp add: App_eq_foldl_conv)
       apply (split split_if_asm)
        apply simp
       apply simp
      apply (drule App_eq_foldl_conv [THEN iffD1])
      apply (split split_if_asm)
       apply simp
       apply blast
      apply (force intro!: disjI1 [THEN append_step1I])
     apply (drule App_eq_foldl_conv [THEN iffD1])
     apply (split split_if_asm)
      apply simp
      apply blast
     by (clarify, auto 0 3 del: exI intro!: exI intro: append_step1I)
    
  with cases show ?thesis by blast
qed

lemma apps_preserves_beta [simp]:
    "r \<rightarrow>\<^sub>\<beta> s ==> r \<degree>\<degree> ss \<rightarrow>\<^sub>\<beta> s \<degree>\<degree> ss"
  by (induct ss rule: rev_induct) auto

lemma apps_preserves_beta2 [simp]:
    "r ->> s ==> r \<degree>\<degree> ss ->> s \<degree>\<degree> ss"
  apply (induct set: rtranclp)
   apply blast
  apply (blast intro: apps_preserves_beta rtranclp.rtrancl_into_rtrancl)
  done

lemma apps_preserves_betas [simp]:
    "rs => ss \<Longrightarrow> r \<degree>\<degree> rs \<rightarrow>\<^sub>\<beta> r \<degree>\<degree> ss"
  apply (induct rs arbitrary: ss rule: rev_induct)
   apply simp
  apply simp
  apply (rule_tac xs = ss in rev_exhaust)
   apply simp
  apply simp
  apply (drule Snoc_step1_SnocD)
  apply blast
  done

subsection {* Terminating lambda terms *}

inductive IT' :: "program_rep => bool" and IT :: "dB => bool"
  where
    Var [intro]: "listsp IT rs ==> IT (Var n \<degree>\<degree> rs)"
  | Lambda [intro]: "IT r ==> IT (Abs r)"
  | Beta [intro]: "IT ((r[s/0]) \<degree>\<degree> ss) ==> IT s ==> IT ((Abs r \<degree> s) \<degree>\<degree> ss)"
  | [intro]: "listsp IT rs ==> IT' body \<Longrightarrow> IT (Proc body args ret \<degree>\<degree> rs)"
  | [intro]: "IT' Skip"

lemma AppAbs_iff: "IT ((Abs r \<degree> s) \<degree>\<degree> ss) = (IT ((r[s/0]) \<degree>\<degree> ss) \<and> IT s)"
  apply (rule iffI)
  apply (cases "((Abs r \<degree> s) \<degree>\<degree> ss)" rule:IT.cases, auto)
  apply (metis Var_apps_neq_Abs_apps foldl_Cons)
  apply (metis Var_apps_neq_Abs_apps foldl_Cons)
  apply (metis (mono_tags) Abs_apps_eq_Abs_apps_conv foldl_Cons list.inject)
  apply (metis (full_types) Abs_apps_eq_Abs_apps_conv append_Cons foldl_Cons last.simps last_appendR not_Cons_self2 rotate1.simps(2))
  apply (metis foldl_Cons Proc_apps_neq_Abs_apps)
by (metis (poly_guards_query) Proc_apps_neq_Abs_apps foldl_Cons)
  

lemma Var_iff: "IT (Var n \<degree>\<degree> rs) = listsp IT rs"
  apply (rule iffI)
  apply (cases "Var n \<degree>\<degree> rs" rule:IT.cases, auto)
  by (metis Var_apps_neq_Abs_apps foldl_Cons)
  
subsection {* Every term in @{text "IT"} terminates *}

lemma double_induction_lemma [rule_format]:
  "termip beta s ==> \<forall>t. termip beta t -->
    (\<forall>r ss. t = r[s/0] \<degree>\<degree> ss --> termip beta (Abs r \<degree> s \<degree>\<degree> ss))"
  apply (erule accp_induct)
  apply (rule allI)
  apply (rule impI)
  apply (erule thin_rl)
  apply (erule accp_induct)
  apply clarify
  apply (rule accp.accI)
  apply (safe elim!: apps_betasE)
    apply (blast intro: subst_preserves_beta apps_preserves_beta)
   apply (blast intro: apps_preserves_beta2 subst_preserves_beta2 rtranclp_converseI
     dest: accp_downwards)  (* FIXME: acc_downwards can be replaced by acc(R ^* ) = acc(r) *)
  apply (blast dest: apps_preserves_betas)
  done

thm accI

lemma tmp: "listsp (termip op \<rightarrow>\<^sub>\<beta>) rs \<Longrightarrow>
       termip op \<longrightarrow>\<^sub>\<beta> body \<Longrightarrow> termip op \<rightarrow>\<^sub>\<beta> (Proc body args ret \<degree>\<degree> rs)"
  apply (induction rs rule:rev_induct, simp_all)
  apply (erule accp_induct[where r="op \<longrightarrow>\<^sub>\<beta>\<inverse>\<inverse>"])
  apply (rule accp.intros, metis beta_cases(4) conversep_iff)
  apply (rule accp.intros)
  unfolding conversep_iff
  apply (cases rule:beta.cases)
  using Abs_App_neq_Proc_apps xxx
using Abs_App_neq_Proc_apps[where ss="x#xs", symmetric]
  apply (rule beta_cases)
  apply (rule accp_downward)
  defer apply simp
apply clarify
  apply (erule beta_cases)
  apply (metisx beta'.simps)
apply (metis (full_types) beta_cases(5) program_rep.exhaust)
apply (metis (poly_guards_query) beta'.simps beta_cases(4))
  apply (metis (mono_tags, hide_lams) beta'.simps beta_cases(4))
    
  apply (drule lists_accD) 
  apply (rule accp_downward)
  defer
  

  apply (drule rev_predicate1D [OF _ listsp_mono [where B="termip beta"]])
    apply (fast intro!: predicate1I)
    apply (drule lists_accD) 
    apply (erule accp_induct)
    apply (rule accp.accI)
    apply simp
    apply (drule head_Proc_reduction)
    apply (erule exE, erule conjE, clarify)
    
thm IT'_IT.inducts
oops
  
lemma IT_implies_termi: "IT t ==> termip beta t"
  apply (induct taking: "termip beta'" set: IT)

    apply (drule rev_predicate1D [OF _ listsp_mono [where B="termip beta"]])
    apply (fast intro!: predicate1I)
    apply (drule lists_accD)
    apply (erule accp_induct)
    apply (rule accp.accI)
    apply (blast dest: head_Var_reduction)
   apply (erule accp_induct)
   apply (rule accp.accI)
   apply blast
  apply (blast intro: double_induction_lemma)

  apply (drule rev_predicate1D [OF _ listsp_mono [where B="termip beta"]])
    apply (fast intro!: predicate1I)
    apply (drule lists_accD) 
    apply (erule accp_induct)
    apply (rule accp.accI)
    using head_Proc_reduction
    apply (blaxst dest: head_Proc_reduction)

term "
\<And>rs n x y.
       Wellfounded.accp (step1 op \<rightarrow>\<^sub>\<beta>\<inverse>\<inverse>) x \<Longrightarrow>
       \<forall>y. step1 op \<rightarrow>\<^sub>\<beta>\<inverse>\<inverse> y x \<longrightarrow> termip op \<rightarrow>\<^sub>\<beta> (Var n \<degree>\<degree> y) \<Longrightarrow>
       op \<rightarrow>\<^sub>\<beta>\<inverse>\<inverse> y (Var n \<degree>\<degree> x) \<Longrightarrow> termip op \<rightarrow>\<^sub>\<beta> y
"
  done



subsection {* Every terminating term is in @{text "IT"} *}

declare Var_apps_neq_Abs_apps [symmetric, simp]

lemma [simp, THEN not_sym, simp]: "Var n \<degree>\<degree> ss \<noteq> Abs r \<degree> s \<degree>\<degree> ts"
  by (simp add: foldl_Cons [symmetric] del: foldl_Cons)

lemma [simp]:
  "(Abs r \<degree> s \<degree>\<degree> ss = Abs r' \<degree> s' \<degree>\<degree> ss') = (r = r' \<and> s = s' \<and> ss = ss')"
  by (simp add: foldl_Cons [symmetric] del: foldl_Cons)

inductive_cases [elim!]:
  "IT (Var n \<degree>\<degree> ss)"
  "IT (Abs t)"
  "IT (Abs r \<degree> s \<degree>\<degree> ts)"
  "IT (Proc body args ret)"

theorem Apps_dB_induct_tmp:
  assumes "!!n ts. \<forall>t \<in> set ts. P t ==> P (Var n \<degree>\<degree> ts)"
    and "!!u ts. [| P u; \<forall>t \<in> set ts. P t |] ==> P (Abs u \<degree>\<degree> ts)"
    and "\<And>body args ret ts. \<lbrakk> P' body; \<forall>t \<in> set ts. P t \<rbrakk> \<Longrightarrow> P (Proc body args ret \<degree>\<degree> ts)"
    and "P' Skip"
  shows "P' p" and "P t"
sorry

(* XXX *)
theorem termi_implies_IT: "termip beta r ==> IT r"
  apply (erule accp_induct)
  apply (rename_tac r)
  apply (erule thin_rl)
  apply (erule rev_mp)
  apply simp
  apply (rule_tac t = r and P' = "\<lambda>p. (\<forall>y. p \<longrightarrow>\<^sub>\<beta> y \<longrightarrow> IT' y) \<longrightarrow> IT' p" in Apps_dB_induct_tmp(2))
   apply clarify (*4*)
   apply (rule IT'_IT.intros) 
   apply clarify
   apply (drule bspec, assumption)
   apply (erule mp)
   apply clarify
   apply (drule_tac r=beta in conversepI)
   apply (drule_tac r="beta^--1" in ex_step1I, assumption)
   apply clarify
   apply (rename_tac us)
   apply (erule_tac x = "Var n \<degree>\<degree> us" in allE)
   apply (drule mp, rule apps_preserves_betas, simp, unfold Var_iff)
   apply force(*3*)
   apply (rename_tac u ts)
   apply (case_tac ts)(*4*)
    apply simp
    apply blast(*3*)
   apply (rename_tac s ss)
   apply simp
   apply clarify
   apply (rule IT'_IT.intros)(*4*)
    apply (blast intro: apps_preserves_beta)(*3*)
   apply (erule mp)
   apply clarify
   apply (rename_tac t)
   apply (erule_tac x = "Abs u \<degree> t \<degree>\<degree> ss" in allE)
   apply (drule_tac Q="IT (App (Abs u) t \<degree>\<degree> ss)" in mp)(*4*)
   apply force(*3*) 
   apply (unfold AppAbs_iff)
   apply force   
   
done

by simp
end 

subsection {* Properties of @{text IT} *}

lemma lift_IT [intro!]: "IT t \<Longrightarrow> IT (lift t i)"
  apply (induct arbitrary: i set: IT)
    apply (simp (no_asm))
    apply (rule conjI)
     apply
      (rule impI,
       rule IT.Var,
       erule listsp.induct,
       simp (no_asm),
       simp (no_asm),
       rule listsp.Cons,
       blast,
       assumption)+
     apply auto
   done

lemma lifts_IT: "listsp IT ts \<Longrightarrow> listsp IT (map (\<lambda>t. lift t 0) ts)"
  by (induct ts) auto

lemma subst_Var_IT: "IT r \<Longrightarrow> IT (r[Var i/j])"
  apply (induct arbitrary: i j set: IT)
    txt {* Case @{term Var}: *}
    apply (simp (no_asm) add: subst_Var)
    apply
    ((rule conjI impI)+,
      rule IT.Var,
      erule listsp.induct,
      simp (no_asm),
      simp (no_asm),
      rule listsp.Cons,
      fast,
      assumption)+
   txt {* Case @{term Lambda}: *}
   apply atomize
   apply simp
   apply (rule IT.Lambda)
   apply fastx
  txt {* Case @{term Beta}: *}
  apply atomize
  apply (simp (no_asm_use) add: subst_subst [symmetric])
  apply (rule IT.Beta)
   apply auto
  done

lemma Var_IT: "IT (Var n)"
  apply (subgoal_tac "IT (Var n \<degree>\<degree> [])")
   apply simp
  apply (rule IT.Var)
  apply (rule listsp.Nil)
  done

lemma app_Var_IT: "IT t \<Longrightarrow> IT (t \<degree> Var i)"
  apply (induct set: IT)
    apply (subst app_last)
    apply (rule IT.Var)
    apply simp
    apply (rule listsp.Cons)
     apply (rule Var_IT)
    apply (rule listsp.Nil)
   apply (rule IT.Beta [where ?ss = "[]", unfolded foldl_Nil [THEN eq_reflection]])
    apply (erule subst_Var_IT)
   apply (rule Var_IT)
  apply (subst app_last)
  apply (rule IT.Beta)
   apply (subst app_last [symmetric])
   apply assumption
  apply assumption
  done


subsection {* Well-typed substitution preserves termination *}

lemma subst_type_IT:
  "\<And>t e T u i. IT t \<Longrightarrow> e\<langle>i:U\<rangle> \<turnstile> t : T \<Longrightarrow>
    IT u \<Longrightarrow> e \<turnstile> u : U \<Longrightarrow> IT (t[u/i])"
  (is "PROP ?P U" is "\<And>t e T u i. _ \<Longrightarrow> PROP ?Q t e T u i U")
proof (induct U)
  fix T t
  assume MI1: "\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> PROP ?P T1"
  assume MI2: "\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> PROP ?P T2"
  assume "IT t"
  thus "\<And>e T' u i. PROP ?Q t e T' u i T"
  proof induct
    fix e T' u i
    assume uIT: "IT u"
    assume uT: "e \<turnstile> u : T"
    {
      case (Var rs n e1 T'1 u1 i1)
      assume nT: "e\<langle>i:T\<rangle> \<turnstile> Var n \<degree>\<degree> rs : T'"
      let ?ty = "\<lambda>t. \<exists>T'. e\<langle>i:T\<rangle> \<turnstile> t : T'"
      let ?R = "\<lambda>t. \<forall>e T' u i.
        e\<langle>i:T\<rangle> \<turnstile> t : T' \<longrightarrow> IT u \<longrightarrow> e \<turnstile> u : T \<longrightarrow> IT (t[u/i])"
      show "IT ((Var n \<degree>\<degree> rs)[u/i])"
      proof (cases "n = i")
        case True
        show ?thesis
        proof (cases rs)
          case Nil
          with uIT True show ?thesis by simp
        next
          case (Cons a as)
          with nT have "e\<langle>i:T\<rangle> \<turnstile> Var n \<degree> a \<degree>\<degree> as : T'" by simp
          then obtain Ts
              where headT: "e\<langle>i:T\<rangle> \<turnstile> Var n \<degree> a : Ts \<Rrightarrow> T'"
              and argsT: "e\<langle>i:T\<rangle> \<tturnstile> as : Ts"
            by (rule list_app_typeE)
          from headT obtain T''
              where varT: "e\<langle>i:T\<rangle> \<turnstile> Var n : T'' \<Rightarrow> Ts \<Rrightarrow> T'"
              and argT: "e\<langle>i:T\<rangle> \<turnstile> a : T''"
            by cases simp_all
          from varT True have T: "T = T'' \<Rightarrow> Ts \<Rrightarrow> T'"
            by cases auto
          with uT have uT': "e \<turnstile> u : T'' \<Rightarrow> Ts \<Rrightarrow> T'" by simp
          from T have "IT ((Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0)
            (map (\<lambda>t. t[u/i]) as))[(u \<degree> a[u/i])/0])"
          proof (rule MI2)
            from T have "IT ((lift u 0 \<degree> Var 0)[a[u/i]/0])"
            proof (rule MI1)
              have "IT (lift u 0)" by (rule lift_IT [OF uIT])
              thus "IT (lift u 0 \<degree> Var 0)" by (rule app_Var_IT)
              show "e\<langle>0:T''\<rangle> \<turnstile> lift u 0 \<degree> Var 0 : Ts \<Rrightarrow> T'"
              proof (rule typing.App)
                show "e\<langle>0:T''\<rangle> \<turnstile> lift u 0 : T'' \<Rightarrow> Ts \<Rrightarrow> T'"
                  by (rule lift_type) (rule uT')
                show "e\<langle>0:T''\<rangle> \<turnstile> Var 0 : T''"
                  by (rule typing.Var) simp
              qed
              from Var have "?R a" by cases (simp_all add: Cons)
              with argT uIT uT show "IT (a[u/i])" by simp
              from argT uT show "e \<turnstile> a[u/i] : T''"
                by (rule subst_lemma) simp
            qed
            thus "IT (u \<degree> a[u/i])" by simp
            from Var have "listsp ?R as"
              by cases (simp_all add: Cons)
            moreover from argsT have "listsp ?ty as"
              by (rule lists_typings)
            ultimately have "listsp (\<lambda>t. ?R t \<and> ?ty t) as"
              by simp
            hence "listsp IT (map (\<lambda>t. lift t 0) (map (\<lambda>t. t[u/i]) as))"
              (is "listsp IT (?ls as)")
            proof induct
              case Nil
              show ?case by fastforce
            next
              case (Cons b bs)
              hence I: "?R b" by simp
              from Cons obtain U where "e\<langle>i:T\<rangle> \<turnstile> b : U" by fast
              with uT uIT I have "IT (b[u/i])" by simp
              hence "IT (lift (b[u/i]) 0)" by (rule lift_IT)
              hence "listsp IT (lift (b[u/i]) 0 # ?ls bs)"
                by (rule listsp.Cons) (rule Cons)
              thus ?case by simp
            qed
            thus "IT (Var 0 \<degree>\<degree> ?ls as)" by (rule IT.Var)
            have "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<turnstile> Var 0 : Ts \<Rrightarrow> T'"
              by (rule typing.Var) simp
            moreover from uT argsT have "e \<tturnstile> map (\<lambda>t. t[u/i]) as : Ts"
              by (rule substs_lemma)
            hence "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<tturnstile> ?ls as : Ts"
              by (rule lift_types)
            ultimately show "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<turnstile> Var 0 \<degree>\<degree> ?ls as : T'"
              by (rule list_app_typeI)
            from argT uT have "e \<turnstile> a[u/i] : T''"
              by (rule subst_lemma) (rule refl)
            with uT' show "e \<turnstile> u \<degree> a[u/i] : Ts \<Rrightarrow> T'"
              by (rule typing.App)
          qed
          with Cons True show ?thesis
            by (simp add: comp_def)
        qed
      next
        case False
        from Var have "listsp ?R rs" by simp
        moreover from nT obtain Ts where "e\<langle>i:T\<rangle> \<tturnstile> rs : Ts"
          by (rule list_app_typeE)
        hence "listsp ?ty rs" by (rule lists_typings)
        ultimately have "listsp (\<lambda>t. ?R t \<and> ?ty t) rs"
          by simp
        hence "listsp IT (map (\<lambda>x. x[u/i]) rs)"
        proof induct
          case Nil
          show ?case by fastforce
        next
          case (Cons a as)
          hence I: "?R a" by simp
          from Cons obtain U where "e\<langle>i:T\<rangle> \<turnstile> a : U" by fast
          with uT uIT I have "IT (a[u/i])" by simp
          hence "listsp IT (a[u/i] # map (\<lambda>t. t[u/i]) as)"
            by (rule listsp.Cons) (rule Cons)
          thus ?case by simp
        qed
        with False show ?thesis by (auto simp add: subst_Var)
      qed
    next
      case (Lambda r e1 T'1 u1 i1)
      assume "e\<langle>i:T\<rangle> \<turnstile> Abs r : T'"
        and "\<And>e T' u i. PROP ?Q r e T' u i T"
      with uIT uT show "IT (Abs r[u/i])"
        by fastforce
    next
      case (Beta r a as e1 T'1 u1 i1)
      assume T: "e\<langle>i:T\<rangle> \<turnstile> Abs r \<degree> a \<degree>\<degree> as : T'"
      assume SI1: "\<And>e T' u i. PROP ?Q (r[a/0] \<degree>\<degree> as) e T' u i T"
      assume SI2: "\<And>e T' u i. PROP ?Q a e T' u i T"
      have "IT (Abs (r[lift u 0/Suc i]) \<degree> a[u/i] \<degree>\<degree> map (\<lambda>t. t[u/i]) as)"
      proof (rule IT.Beta)
        have "Abs r \<degree> a \<degree>\<degree> as \<rightarrow>\<^sub>\<beta> r[a/0] \<degree>\<degree> as"
          by (rule apps_preserves_beta) (rule beta.beta)
        with T have "e\<langle>i:T\<rangle> \<turnstile> r[a/0] \<degree>\<degree> as : T'"
          by (rule subject_reduction)
        hence "IT ((r[a/0] \<degree>\<degree> as)[u/i])"
          using uIT uT by (rule SI1)
        thus "IT (r[lift u 0/Suc i][a[u/i]/0] \<degree>\<degree> map (\<lambda>t. t[u/i]) as)"
          by (simp del: subst_map add: subst_subst subst_map [symmetric])
        from T obtain U where "e\<langle>i:T\<rangle> \<turnstile> Abs r \<degree> a : U"
          by (rule list_app_typeE) fast
        then obtain T'' where "e\<langle>i:T\<rangle> \<turnstile> a : T''" by cases simp_all
        thus "IT (a[u/i])" using uIT uT by (rule SI2)
      qed
      thus "IT ((Abs r \<degree> a \<degree>\<degree> as)[u/i])" by simp
    }
  qed
qed


subsection {* Well-typed terms are strongly normalizing *}

lemma type_implies_IT:
  assumes "e \<turnstile> t : T"
  shows "IT t"
  using assms
proof induct
  case Var
  show ?case by (rule Var_IT)
next
  case Abs
  show ?case by (rule IT.Lambda) (rule Abs)
next
  case (App e s T U t)
  have "IT ((Var 0 \<degree> lift t 0)[s/0])"
  proof (rule subst_type_IT)
    have "IT (lift t 0)" using `IT t` by (rule lift_IT)
    hence "listsp IT [lift t 0]" by (rule listsp.Cons) (rule listsp.Nil)
    hence "IT (Var 0 \<degree>\<degree> [lift t 0])" by (rule IT.Var)
    also have "Var 0 \<degree>\<degree> [lift t 0] = Var 0 \<degree> lift t 0" by simp
    finally show "IT \<dots>" .
    have "e\<langle>0:T \<Rightarrow> U\<rangle> \<turnstile> Var 0 : T \<Rightarrow> U"
      by (rule typing.Var) simp
    moreover have "e\<langle>0:T \<Rightarrow> U\<rangle> \<turnstile> lift t 0 : T"
      by (rule lift_type) (rule App.hyps)
    ultimately show "e\<langle>0:T \<Rightarrow> U\<rangle> \<turnstile> Var 0 \<degree> lift t 0 : U"
      by (rule typing.App)
    show "IT s" by fact
    show "e \<turnstile> s : T \<Rightarrow> U" by fact
  qed
  thus ?case by simp
qed

theorem type_implies_termi: "e \<turnstile> t : T \<Longrightarrow> termip beta t"
proof -
  assume "e \<turnstile> t : T"
  hence "IT t" by (rule type_implies_IT)
  thus ?thesis by (rule IT_implies_termi)
qed

