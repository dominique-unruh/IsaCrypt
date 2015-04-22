theory TypedLambda2
imports Main Tools "~~/src/HOL/Proofs/Lambda/ListOrder"
begin

declare [[syntax_ambiguity_warning = false]]


subsection {* Lambda-terms in de Bruijn notation and substitution *}

datatype dB =
    Var nat
  | App dB dB (infixl "\<degree>" 200)
  | Abs dB
(*  | Pair dB dB
  | Unpair bool dB*)

primrec
  lift :: "[dB, nat] => dB"
where
    "lift (Var i) k = (if i < k then Var i else Var (i + 1))"
  | "lift (s \<degree> t) k = lift s k \<degree> lift t k"
  | "lift (Abs s) k = Abs (lift s (k + 1))"

primrec
  subst :: "[dB, dB, nat] => dB"  ("_[_'/_]" [300, 0, 0] 300)
where (* FIXME base names *)
    subst_Var: "(Var i)[s/k] =
      (if k < i then Var (i - 1) else if i = k then s else Var i)"
  | subst_App: "(t \<degree> u)[s/k] = t[s/k] \<degree> u[s/k]"
  | subst_Abs: "(Abs t)[s/k] = Abs (t[lift s 0 / k+1])"

declare subst_Var [simp del]

subsection {* Beta-reduction *}

inductive beta :: "[dB, dB] => bool"  (infixl "\<rightarrow>\<^sub>\<beta>" 50)
  where
    beta [simp, intro!]: "Abs s \<degree> t \<rightarrow>\<^sub>\<beta> s[t/0]"
  | appL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> s \<degree> u \<rightarrow>\<^sub>\<beta> t \<degree> u"
  | appR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> u \<degree> s \<rightarrow>\<^sub>\<beta> u \<degree> t"
  | abs [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> Abs s \<rightarrow>\<^sub>\<beta> Abs t"

abbreviation
  beta_reds :: "[dB, dB] => bool"  (infixl "->>" 50) where
  "s ->> t == beta^** s t"

notation (latex)
  beta_reds  (infixl "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50)

inductive_cases beta_cases [elim!]:
  "Var i \<rightarrow>\<^sub>\<beta> t"
  "Abs r \<rightarrow>\<^sub>\<beta> s"
  "s \<degree> t \<rightarrow>\<^sub>\<beta> u"

declare if_not_P [simp] not_less_eq [simp]
  -- {* don't add @{text "r_into_rtrancl[intro!]"} *}


subsection {* Congruence rules *}

lemma rtrancl_beta_Abs [intro!]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' ==> Abs s \<rightarrow>\<^sub>\<beta>\<^sup>* Abs s'"
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
    "i < k + 1 \<Longrightarrow> lift (lift t i) (Suc k) = lift (lift t k) i"
  by (induct t arbitrary: i k) auto

lemma lift_subst [simp]:
    "j < i + 1 \<Longrightarrow> lift (t[s/j]) i = (lift t (i + 1)) [lift s i / j]"
  by (induct t arbitrary: i j s)
    (simp_all add: diff_Suc subst_Var lift_lift split: nat.split)

lemma lift_subst_lt:
    "i < j + 1 \<Longrightarrow> lift (t[s/j]) i = (lift t i) [lift s i / j + 1]"
  by (induct t arbitrary: i j s) (simp_all add: subst_Var lift_lift)

lemma subst_lift [simp]:
    "(lift t k)[s/k] = t"
  by (induct t arbitrary: k s) simp_all

lemma subst_subst:
    "i < j + 1 \<Longrightarrow> t[lift v i / Suc j][u[v/j]/i] = t[u/i][v/j]"
  by (induct t arbitrary: i j u v)
    (simp_all add: diff_Suc subst_Var lift_lift [symmetric] lift_subst_lt
      split: nat.split)


subsection {* Preservation theorems *}

text {* Not used in Church-Rosser proof, but in Strong
  Normalization. \medskip *}

theorem subst_preserves_beta [simp]:
    "r \<rightarrow>\<^sub>\<beta> s ==> r[t/i] \<rightarrow>\<^sub>\<beta> s[t/i]"
  by (induct arbitrary: t i set: beta) (simp_all add: subst_subst [symmetric])

theorem lift_preserves_beta [simp]:
    "r \<rightarrow>\<^sub>\<beta> s ==> lift r i \<rightarrow>\<^sub>\<beta> lift s i"
  by (induct arbitrary: i set: beta) auto


theorem subst_preserves_beta2 [simp]: "r \<rightarrow>\<^sub>\<beta> s ==> t[r/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t[s/i]"
  apply (induct t arbitrary: r s i)
    close (simp add: subst_Var r_into_rtranclp)
   close (simp add: rtrancl_beta_App)
  by (simp add: rtrancl_beta_Abs)


abbreviation
  list_application :: "dB => dB list => dB"  (infixl "\<degree>\<degree>" 150) where
  "t \<degree>\<degree> ts == foldl (op \<degree>) t ts"


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


lemma lift_map [simp]:
    "lift (t \<degree>\<degree> ts) i = lift t i \<degree>\<degree> map (\<lambda>t. lift t i) ts"
  by (induct ts arbitrary: t) simp_all

lemma subst_map [simp]:
    "subst (t \<degree>\<degree> ts) u i = subst t u i \<degree>\<degree> map (\<lambda>t. subst t u i) ts"
  by (induct ts arbitrary: t) simp_all

lemma app_last: "(t \<degree>\<degree> ts) \<degree> u = t \<degree>\<degree> (ts @ [u])"
  by simp




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
  | Prod type type

inductive typing :: "(nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile> _ : _" [50, 50, 50] 50)
  where
    Var [intro!]: "env x = T \<Longrightarrow> env \<turnstile> Var x : T"
  | Abs [intro!]: "env\<langle>0:T\<rangle> \<turnstile> t : U \<Longrightarrow> env \<turnstile> Abs t : (T \<Rightarrow> U)"
  | App [intro!]: "env \<turnstile> s : T \<Rightarrow> U \<Longrightarrow> env \<turnstile> t : T \<Longrightarrow> env \<turnstile> (s \<degree> t) : U"
  | Pair [intro!]: "\<lbrakk> env \<turnstile> s : T; env \<turnstile> t : U \<rbrakk> \<Longrightarrow> 
        env \<turnstile> Abs ((Var 0) \<degree> (lift s 0) \<degree> (lift t 0)) : Prod T U"
  | Fst [intro!]: "env \<turnstile> Abs (Var 0 \<degree> Abs (Abs (Var 1))) : Prod T U \<Rightarrow> T"

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



subsection {* Lifting preserves well-typedness *}

lemma lift_type [intro!]: "e \<turnstile> t : T \<Longrightarrow> e\<langle>i:U\<rangle> \<turnstile> lift t i : T"
  apply (induct arbitrary: i U set: typing, auto) 
  by (subst lift_lift, auto)+


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
  close blast
  by (subst lift_subst_lt[simplified,symmetric], auto)+ 
  

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


lemma reduce_below_lift:
  assumes "lift s' k \<rightarrow>\<^sub>\<beta> t"
  shows "\<exists>t'. t = lift t' k \<and> s' \<rightarrow>\<^sub>\<beta> t'"
proof -
def s == "lift s' k"
from assms have st: "s \<rightarrow>\<^sub>\<beta> t" unfolding s_def by simp
have "\<And>s' k. s=lift s' k \<Longrightarrow> \<exists>t'. t = lift t' k \<and> s' \<rightarrow>\<^sub>\<beta> t'"
  using st proof (induction)
  case (abs s t) 
    obtain s0 where "s'=Abs s0" and "s = lift s0 (Suc k)"
      apply (atomize_elim)
      apply (cases s')
      using `Abs s = lift s' k` apply auto
      by (metis dB.distinct(3))
    with abs.IH obtain t' where "t = lift t' (Suc k)" and "s0 \<rightarrow>\<^sub>\<beta> t'" by auto
    show ?case apply (rule exI[of _ "Abs t'"], auto)
      apply (metis `t = lift t' (Suc k)`)
      by (metis `s' = Abs s0` `s0 \<rightarrow>\<^sub>\<beta> t'` beta.abs)
  next case (appL s t u)
    obtain s0 u0 where s':"s'=s0 \<degree> u0" 
          and s:"s = lift s0 k" and u:"u = lift u0 k"
      by (metis appL.prems dB.distinct(1) dB.distinct(5) dB.exhaust dB.inject(2) lift.simps(2) subst_App subst_lift)
    with appL.IH obtain t' where t:"t = lift t' k" and s0: "s0 \<rightarrow>\<^sub>\<beta> t'" by auto
    show ?case apply (rule exI[of _ "t' \<degree> u0"], auto) 
      close (fact t) close (fact u)
      by (metis (full_types) s' s0 beta.appL)
  next case (appR s t u)
    obtain s0 u0 where s':"s'=u0 \<degree> s0" 
          and s:"s = lift s0 k" and u:"u = lift u0 k"
      by (metis appR.prems dB.distinct(1) dB.distinct(6) dB.exhaust dB.inject(2) lift.simps(2) subst_App subst_lift)
    with appR.IH obtain t' where t:"t = lift t' k" and s0: "s0 \<rightarrow>\<^sub>\<beta> t'" by auto
    show ?case apply (rule exI[of _ "u0 \<degree> t'"], auto) 
      close (fact u) close (fact t) 
      by (metis (full_types) s' s0 beta.appR)
  next case (beta s t)
    then obtain s0 t0 where s':"s'=Abs s0 \<degree> t0" 
        and s:"s=lift s0 (Suc k)" and t:"t=lift t0 k" 
      apply (atomize_elim)
      apply (cases s')
      close (metis beta.beta beta_cases(1) subst_lift subst_preserves_beta) 
      defer close auto
      apply (rename_tac s0' t0', case_tac s0')
      defer close auto close auto
      by (metis dB.distinct(3) dB.inject(2) lift.simps(2) subst_Abs subst_lift)
    show "\<exists>t'. s[t/0] = lift t' k \<and> s' \<rightarrow>\<^sub>\<beta> t'"
      apply (rule exI[of _ "s0[t0/0]"])
      by (auto simp: s t s')
  qed
  with s_def show ?thesis by auto
qed

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
    apply (frule reduce_below_lift, auto)
    by (frule reduce_below_lift, auto)



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
next
  case Prod
  show ?case by (rule assms) (insert Prod, simp_all)
qed


text {*
  Lifting beta-reduction to lists of terms, reducing exactly one element.
*}

abbreviation
  list_beta :: "dB list => dB list => bool"  (infixl "=>" 50) where
  "rs => ss == step1 beta rs ss"

lemma head_Var_reduction:
  "Var n \<degree>\<degree> rs \<rightarrow>\<^sub>\<beta> v \<Longrightarrow> \<exists>ss. rs => ss \<and> v = Var n \<degree>\<degree> ss"
  apply (induct u == "Var n \<degree>\<degree> rs" v arbitrary: rs set: beta)
     close simp
    apply (rule_tac xs = rs in rev_exhaust)
     close simp
    close (atomize, force intro: append_step1I)
   apply (rule_tac xs = rs in rev_exhaust)
    close simp
    apply (auto 0 3 intro: disjI2 [THEN append_step1I])
  done

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
  proof (induct u == "r \<degree>\<degree> rs" s arbitrary: r rs set: beta)
  case beta thus ?case
       apply (case_tac r)
         close simp
        apply (simp add: App_eq_foldl_conv)
        apply (split split_if_asm)
         apply simp
         close blast
        close simp
       apply (simp add: App_eq_foldl_conv)
       apply (split split_if_asm)
        close simp
       by simp
  next case appL thus ?case
      apply auto
      apply (drule App_eq_foldl_conv [THEN iffD1])
      apply (split split_if_asm)
       apply simp
       close blast
      by (force intro!: disjI1 [THEN append_step1I])
  next case appR thus ?case
     apply auto
     apply (drule App_eq_foldl_conv [THEN iffD1])
     apply (split split_if_asm)
      apply simp
      close blast
     by (clarify, auto 0 3 del: exI intro!: exI intro: append_step1I)
  next case abs thus ?case by auto
  qed
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

inductive IT :: "dB => bool"
  where
    Var [intro]: "listsp IT rs ==> IT (Var n \<degree>\<degree> rs)"
  | Lambda [intro]: "IT r ==> IT (Abs r)"
  | Beta [intro]: "IT ((r[s/0]) \<degree>\<degree> ss) ==> IT s ==> IT ((Abs r \<degree> s) \<degree>\<degree> ss)"


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
  apply (safe del: apps_betasE elim!: apps_betasE)
    apply (blast intro: subst_preserves_beta apps_preserves_beta)
   apply (blast intro: apps_preserves_beta2 subst_preserves_beta2 rtranclp_converseI
     dest: accp_downwards)  (* FIXME: acc_downwards can be replaced by acc(R ^* ) = acc(r) *)
  apply (blast dest: apps_preserves_betas)
  done

lemma IT_implies_termi: "IT t ==> termip beta t"
proof (induct set: IT)
case Var thus ?case 
    apply (drule_tac rev_predicate1D [OF _ listsp_mono [where B="termip beta"]])
    close (fast del: predicate1I intro!: predicate1I)
    apply (drule lists_accD)
    apply (erule accp_induct)
    apply (rule accp.accI)
    by (blast dest: head_Var_reduction)
next case Lambda thus ?case
   apply (erule_tac accp_induct)
   apply (rule accp.accI)
   by blast
next case Beta thus ?case
  by (blast intro: double_induction_lemma)
qed


subsection {* Every terminating term is in @{text "IT"} *}


lemma [simp]:
  "(Abs r \<degree> s \<degree>\<degree> ss = Abs r' \<degree> s' \<degree>\<degree> ss') = (r = r' \<and> s = s' \<and> ss = ss')"
  by (simp add: foldl_Cons [symmetric] del: foldl_Cons)

inductive_cases [elim!]:
  "IT (Var n \<degree>\<degree> ss)"
  "IT (Abs t)"
  "IT (Abs r \<degree> s \<degree>\<degree> ts)"

(*
theorem termi_implies_IT: "termip beta r ==> IT r"
  apply (erule accp_induct)
  apply (rename_tac r)
  apply (erule thin_rl)
  apply (erule rev_mp)
  apply simp
  apply (rule_tac t = r in Apps_dB_induct)
   apply clarify
   apply (rule IT.intros)
   apply clarify
   apply (drule bspec, assumption)
   apply (erule mp)
   apply clarify
   apply (drule_tac r=beta in conversepI)
   apply (drule_tac r="beta^--1" in ex_step1I, assumption)
   apply clarify
   apply (rename_tac us)
   apply (erule_tac x = "Var n \<degree>\<degree> us" in allE)
   apply force
   apply (rename_tac u ts)
   apply (case_tac ts)
    apply simp
    apply blast
   apply (rename_tac s ss)
   apply simp
   apply clarify
   apply (rule IT.intros)
    apply (blast intro: apps_preserves_beta)
   apply (erule mp)
   apply clarify
   apply (rename_tac t)
   apply (erule_tac x = "Abs u \<degree> t \<degree>\<degree> ss" in allE)
   apply force
   done
*)

text {*
Formalization by Stefan Berghofer. Partly based on a paper proof by
Felix Joachimski and Ralph Matthes \cite{Matthes-Joachimski-AML}.
*}


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
   apply fast
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
proof (induct set: IT)
case Var thus ?case
    apply (subst app_last)
    apply (rule IT.Var)
    apply simp
    apply (rule listsp.Cons)
     close (rule Var_IT)
    by (rule listsp.Nil)
next case Lambda show ?case
  apply (insert Lambda)
  apply (rule IT.Beta [where ?ss = "[]", unfolded foldl_Nil [THEN eq_reflection]])
  close (erule subst_Var_IT)
  by (rule Var_IT)
next case Beta thus ?case
  apply (subst app_last)
  apply (rule IT.Beta)
   apply (subst app_last [symmetric])
   close assumption
  by assumption
qed

subsection {* Well-typed substitution preserves termination *}

lemma remove_product_type:
  assumes "e \<turnstile> Abs r : T'"
  shows "\<exists>A B. e \<turnstile> Abs r : A \<Rightarrow> B"
using assms apply (cases, auto)
  apply (rename_tac x X y Y)
  apply (rule_tac x="X \<Rightarrow> Y \<Rightarrow> Atom 0" in  exI)
  by (rule_tac x="Atom 0" in  exI, auto)

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
        then obtain A B where AB:"e\<langle>i:T\<rangle> \<turnstile> Abs r : A \<Rightarrow> B" 
          by (atomize_elim, rule remove_product_type)
        assume "\<And>e T' u i. PROP ?Q r e T' u i T"
      with AB uIT uT show "IT (Abs r[u/i])"
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
next
  case (Pair env s T t U) 
  have "IT (Abs (Var 0 \<degree>\<degree> [lift s 0, lift t 0]))"
    apply (rule IT.intros)+
    using Pair by auto
  thus ?case by auto
qed

theorem type_implies_termi: "e \<turnstile> t : T \<Longrightarrow> termip beta t"
proof -
  assume "e \<turnstile> t : T"
  hence "IT t" by (rule type_implies_IT)
  thus ?thesis by (rule IT_implies_termi)
qed

end
