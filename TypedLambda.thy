theory TypedLambda
imports Main Tools "~~/src/HOL/Proofs/Lambda/ListOrder" TypedLambdaNominal
begin

locale typed_lambda begin (* to hide syntax *)

declare [[syntax_ambiguity_warning = false]]

subsection {* Lambda-terms in de Bruijn notation and substitution *}

datatype dB =
    Var nat
  | App dB dB (infixl "\<degree>" 200)
  | Abs dB
  | MkPair dB dB
  | Unpair bool dB

primrec
  lift :: "[dB, nat] => dB"
where
    "lift (Var i) k = (if i < k then Var i else Var (i + 1))"
  | "lift (s \<degree> t) k = lift s k \<degree> lift t k"
  | "lift (Abs s) k = Abs (lift s (k + 1))"
  | "lift (MkPair s t) k = MkPair (lift s k) (lift t k)"
  | "lift (Unpair b s) k = Unpair b (lift s k)" 

primrec
  subst :: "[dB, dB, nat] => dB"  ("_[_'/_]" [300, 0, 0] 300)
where (* FIXME base names *)
    subst_Var: "(Var i)[s/k] =
      (if k < i then Var (i - 1) else if i = k then s else Var i)"
  | subst_App: "(t \<degree> u)[s/k] = t[s/k] \<degree> u[s/k]"
  | subst_Abs: "(Abs t)[s/k] = Abs (t[lift s 0 / k+1])"
  | subst_MkPair: "(MkPair t u)[s/k] = MkPair (t[s/k]) (u[s/k])"
  | subst_Unpair: "(Unpair b t)[s/k] = Unpair b (t[s/k])"

declare subst_Var [simp del]

subsection {* Beta-reduction *}

inductive beta :: "[dB, dB] => bool"  (infixl "\<rightarrow>\<^sub>\<beta>" 50)
  where
    beta [simp, intro!]: "Abs s \<degree> t \<rightarrow>\<^sub>\<beta> s[t/0]"
  | appL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> s \<degree> u \<rightarrow>\<^sub>\<beta> t \<degree> u"
  | appR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> u \<degree> s \<rightarrow>\<^sub>\<beta> u \<degree> t"
  | abs [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> Abs s \<rightarrow>\<^sub>\<beta> Abs t"
  | pairL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> MkPair s u \<rightarrow>\<^sub>\<beta> MkPair t u"
  | pairR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> MkPair u s \<rightarrow>\<^sub>\<beta> MkPair u t"
  | unpair [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t ==> Unpair b s \<rightarrow>\<^sub>\<beta> Unpair b t"
  | fst [simp, intro!]: "Unpair True (MkPair s t) \<rightarrow>\<^sub>\<beta> s"
  | snd [simp, intro!]: "Unpair False (MkPair s t) \<rightarrow>\<^sub>\<beta> t"

abbreviation
  beta_reds :: "[dB, dB] => bool"  (infixl "->>" 50) where
  "s ->> t == beta^** s t"

notation (latex)
  beta_reds  (infixl "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50)

inductive_cases beta_cases [elim!]:
  "Var i \<rightarrow>\<^sub>\<beta> t"
  "Abs r \<rightarrow>\<^sub>\<beta> s"
  "s \<degree> t \<rightarrow>\<^sub>\<beta> u"
  "MkPair s t \<rightarrow>\<^sub>\<beta> u"
  "Unpair b t \<rightarrow>\<^sub>\<beta> u"

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

lemma rtrancl_beta_MkPairL:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' ==> MkPair s t \<rightarrow>\<^sub>\<beta>\<^sup>* MkPair s' t"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_MkPairR:
    "t \<rightarrow>\<^sub>\<beta>\<^sup>* t' ==> MkPair s t \<rightarrow>\<^sub>\<beta>\<^sup>* MkPair s t'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

lemma rtrancl_beta_MkPair [intro]:
    "[| s \<rightarrow>\<^sub>\<beta>\<^sup>* s'; t \<rightarrow>\<^sub>\<beta>\<^sup>* t' |] ==> MkPair s t \<rightarrow>\<^sub>\<beta>\<^sup>* MkPair s' t'"
  by (blast intro!: rtrancl_beta_MkPairL rtrancl_beta_MkPairR intro: rtranclp_trans)

lemma rtrancl_beta_Unpair [intro!]:
    "s \<rightarrow>\<^sub>\<beta>\<^sup>* s' ==> Unpair b s \<rightarrow>\<^sub>\<beta>\<^sup>* Unpair b s'"
  by (induct set: rtranclp) (blast intro: rtranclp.rtrancl_into_rtrancl)+

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
  close (simp add: rtrancl_beta_Abs)
  close (simp add: rtrancl_beta_MkPair)
  by (simp add: rtrancl_beta_Unpair)


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

lemma MkPair_eq_apps_conv [iff]:
    "(MkPair p q = s \<degree>\<degree> ss) = (MkPair p q = s \<and> ss = [])"
  by (induct ss rule: rev_induct) auto

lemma Unpair_eq_apps_conv [iff]:
    "(Unpair b p = s \<degree>\<degree> ss) = (Unpair b p = s \<and> ss = [])"
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

datatype lambda_type =
    Atom nat
  | Fun lambda_type lambda_type    (infixr "\<Rightarrow>" 200)
  | Prod lambda_type lambda_type

inductive typing :: "(nat \<Rightarrow> lambda_type) \<Rightarrow> dB \<Rightarrow> lambda_type \<Rightarrow> bool"  ("_ \<turnstile> _ : _" [50, 50, 50] 50)
  where
    Var [intro!]: "env x = T \<Longrightarrow> env \<turnstile> Var x : T"
  | Abs [intro!]: "env\<langle>0:T\<rangle> \<turnstile> t : U \<Longrightarrow> env \<turnstile> Abs t : (T \<Rightarrow> U)"
  | App [intro!]: "env \<turnstile> s : T \<Rightarrow> U \<Longrightarrow> env \<turnstile> t : T \<Longrightarrow> env \<turnstile> (s \<degree> t) : U"
  | MkPair [intro!]: "env \<turnstile> s : T \<Longrightarrow> env \<turnstile> t : U \<Longrightarrow> env \<turnstile> (MkPair s t) : (Prod T U)"
  | Fst [intro!]: "env \<turnstile> s : Prod T U \<Longrightarrow> env \<turnstile> Unpair True s : T"
  | Snd [intro!]: "env \<turnstile> s : Prod T U \<Longrightarrow> env \<turnstile> Unpair False s : U"

inductive_cases typing_elims [elim!]:
  "e \<turnstile> Var i : T"
  "e \<turnstile> t \<degree> u : T"
  "e \<turnstile> Abs t : T"
  "e \<turnstile> MkPair s t : T"
  "e \<turnstile> Unpair b t : T"

primrec
  typings :: "(nat \<Rightarrow> lambda_type) \<Rightarrow> dB list \<Rightarrow> lambda_type list \<Rightarrow> bool"
where
    "typings e [] Ts = (Ts = [])"
  | "typings e (t # ts) Ts =
      (case Ts of
        [] \<Rightarrow> False
      | T # Ts \<Rightarrow> e \<turnstile> t : T \<and> typings e ts Ts)"

abbreviation
  typings_rel :: "(nat \<Rightarrow> lambda_type) \<Rightarrow> dB list \<Rightarrow> lambda_type list \<Rightarrow> bool"
    ("_ ||- _ : _" [50, 50, 50] 50) where
  "env ||- ts : Ts == typings env ts Ts"

notation (latex)
  typings_rel  ("_ \<tturnstile> _ : _" [50, 50, 50] 50)

abbreviation
  funs :: "lambda_type list \<Rightarrow> lambda_type \<Rightarrow> lambda_type"  (infixr "=>>" 200) where
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

lemma apps_betasE [elim!, consumes 1, case_names head tail beta]:
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
        apply (split if_split_asm)
         apply simp
         close blast
        close simp

       apply (simp add: App_eq_foldl_conv)
       apply (split if_split_asm)
        close simp
       close simp

       apply (simp add: App_eq_foldl_conv)
       apply (split if_split_asm)
        close simp
       close simp

       apply (simp add: App_eq_foldl_conv)
       apply (split if_split_asm)
        close simp
       by simp
  next case appL thus ?case
      apply auto
      apply (drule App_eq_foldl_conv [THEN iffD1])
      apply (split if_split_asm)
       apply simp
       close blast
      by (force intro!: disjI1 [THEN append_step1I])
  next case appR thus ?case
     apply auto
     apply (drule App_eq_foldl_conv [THEN iffD1])
     apply (split if_split_asm)
      apply simp
      close blast
     by (clarify, auto 0 3 del: exI intro!: exI intro: append_step1I)
  next case abs thus ?case by auto
  next case unpair thus ?case by auto
  next case fst thus ?case by auto
  next case snd thus ?case by auto
  next case pairL thus ?case by auto
  next case pairR thus ?case by auto
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

subsection {* Reducting strong normalization to strong normalization in nominal *}

definition "fresh_name (xs::name list) = (SOME x::name. x \<sharp> xs)"
lemma fresh_name: "fresh_name (xs::name list) \<sharp> xs"
  unfolding fresh_name_def apply (rule someI_ex) apply (rule exists_fresh') by finite_guess

fun dB_to_lam :: "name list \<Rightarrow> dB \<Rightarrow> lam" where
  "dB_to_lam n (Var i) = (if i<length n then TypedLambdaNominal.Var (n!i) else Lam[undefined]. TypedLambdaNominal.Var undefined)" (* If i too big, use arbitrary closed term, to avoid inventing names *)
| "dB_to_lam n (Abs p) = (let x = fresh_name n in Lam[x].(dB_to_lam (x#n) p))"
| "dB_to_lam n (App p q) = TypedLambdaNominal.App (dB_to_lam n p) (dB_to_lam n q)"
| "dB_to_lam n (MkPair p q) = TypedLambdaNominal.MkPair (dB_to_lam n p) (dB_to_lam n q)"
| "dB_to_lam n (Unpair b p) = TypedLambdaNominal.Unpair b (dB_to_lam n p)"

lemma fresh_list': "(x) \<sharp> ts \<Longrightarrow> (t) \<in> set ts \<Longrightarrow> x \<sharp> t"
  apply (induction ts) by (auto simp: fresh_list_cons)

lemma fresh_id [simp]: shows "(x::name) \<sharp> [y]. TypedLambdaNominal.Var y" and "(x::name) \<sharp> Lam[y]. TypedLambdaNominal.Var y" 
  by (auto simp: abs_fresh fresh_atm)

(* lemma perm_one: "((x::name,y) # \<theta>) \<bullet> t = swap (x,y) (\<theta> \<bullet> t)"
by (simp add: calc_atm(1)) *)

(* find_theorems "?\<theta> \<bullet> ?t = ?t" *)

lemma permute_id [simp]:
  shows "(\<theta>::name prm) \<bullet> ([y]. lam.Var y) = [y]. lam.Var y" (is ?thesis1)
    and "\<theta> \<bullet> Lam[y]. lam.Var y = Lam[y]. lam.Var y" (is ?thesis2)
apply auto
apply (smt abs_fun_pi alpha' at_name_inst fresh_atm lam.fresh(1) lam.perm(1) pt_name_inst swap_simps(2))
by (simp add: TypedLambdaNominal.name_prm_name_def alpha fresh_atm lam.inject(3))

lemma id_undefined: 
  assumes "NO_MATCH undefined y"
  shows "[y]. lam.Var y = [undefined]. lam.Var undefined" (is ?thesis1)
    and "Lam[y]. lam.Var y = Lam[undefined]. lam.Var undefined" (is ?thesis2)
proof -
  show ?thesis1
    by (smt alpha' fresh_atm lam.fresh(1) lam.perm(1) swap_simps(2)) 
  thus ?thesis2
    by (simp add: lam.inject(3))     
qed

thm id_undefined
(*
proof - 
  show ?thesis1
    apply (induction \<theta>) close
    apply auto apply (subst at_prm_fresh)
thm at_prm_fresh
thm at2

find_theorems "(_#_) \<bullet> _ = swap _ _"
  thm calc_atm *)

lemma fresh_dB_to_lam: 
  assumes "(x::name) \<sharp> n"
  shows "x \<sharp> dB_to_lam n p"
using assms proof (induction p arbitrary: n)
case (Var i n) 
  show ?case
  proof auto
    assume "i < length n" 
    hence "n!i \<in> set n" by auto
    with Var show "x \<sharp> n!i" 
      by (rule fresh_list')
  qed
next case (Abs p)
  define y where "y == fresh_name n" 
  have "dB_to_lam n (Abs p) = Lam [y].dB_to_lam (y#n) p"
    by (simp add: Let_def y_def)
  also have "x \<sharp> \<dots>"
    unfolding lam.fresh abs_fresh
    apply (cases "x=y")
     apply simp
    apply simp
    apply (rule Abs.IH)
    unfolding fresh_list_cons
    using Abs.prems fresh_atm by auto
  finally show ?case by simp
qed (auto simp: abs_fresh fresh_bool)

fun typ_conv :: "lambda_type \<Rightarrow> ty" where
  "typ_conv (Atom i) = TVar i"
| "typ_conv (Fun t u) = TArr (typ_conv t) (typ_conv u)"
| "typ_conv (Prod t u) = TPair (typ_conv t) (typ_conv u)"

lemma fresh_distinct [simp]: 
  fixes x :: name
  assumes "x\<sharp>xs"
  assumes "distinct xs"
  shows "distinct (x#xs)"
using assms proof (induction xs arbitrary: x) 
case Nil show ?case by simp
next case (Cons x' xs) 
  hence "x \<sharp> x'" and "x \<sharp> xs" unfolding fresh_list_cons by auto
  from \<open>x \<sharp> x'\<close> have "x \<noteq> x'" using fresh_atm by auto
  from \<open>x \<sharp> xs\<close> have "x \<notin> set xs" using Cons by auto
  have "x' \<notin> set xs" using Cons by simp
  have "distinct xs" using Cons by simp
  show ?case
    using \<open>x\<noteq>x'\<close> \<open>x\<notin>set xs\<close> \<open>x'\<notin>set xs\<close> \<open>distinct xs\<close> by auto 
qed

lemma fresh_zip [simp]: 
  assumes "(x::name) \<sharp> l1" and "x \<sharp> l2" shows "x \<sharp> zip l1 l2"
using assms proof (induction l2 arbitrary: l1)
case Nil show ?case by (simp add: fresh_list_nil)
next case Cons2: (Cons x2 l2)
  thus ?case 
  proof (cases l1)
  case Nil thus ?thesis by (simp add: fresh_list_nil)
  next case (Cons x1 l1')
    from `x \<sharp> l1` have xl1: "x \<sharp> l1'" using `l1 = x1 # l1'` by (auto simp: fresh_list_cons)
    have xl2: "x \<sharp> l2"       using Cons2.prems(2) fresh_list_cons by force
    have fr1: "x \<sharp> (x1, x2)"
      by (metis Cons2.prems(1) Cons2.prems(2) fresh_list_cons fresh_prod local.Cons)
    have fr2: "x \<sharp> zip l1' l2"
      using xl1 xl2 by (rule Cons2.IH)
    show ?thesis unfolding Cons using fr1 fr2 by (auto simp: fresh_list_cons)
  qed
qed

lemma fresh_ty_list [simp]: "(x::name) \<sharp> (ty :: ty list)"
  apply (induction ty)
   close (simp add: fresh_list_nil)
  apply (subst fresh_list_cons, auto)
  by (rule fresh_ty)

lemma fresh_list: "(x::name) \<notin> set l \<Longrightarrow> x \<sharp> l"
  apply (induction l)
  by (auto simp: fresh_list_cons fresh_atm fresh_list_nil)

lemma valid_zip: "distinct names \<Longrightarrow> valid (zip names E)"
  apply (induction names arbitrary: E)
   close
  apply (case_tac E)
   close
  by (auto del: v2 intro!: v2 fresh_zip fresh_list)

fun map_index' :: "nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_index' n f [] = []"
| "map_index' n f (x#xs) = f n x # map_index' (Suc n) f xs"
abbreviation "map_index == map_index' 0"

fun env_conv where
  "env_conv E [] = []"
| "env_conv E (x#xs) = (x,typ_conv (E 0)) # env_conv (\<lambda>i. E (Suc i)) xs"

lemma fresh_env_conv [intro]: "(n::name) \<sharp> names \<Longrightarrow> n \<sharp> env_conv E names"
apply (induction names arbitrary: E) by (auto simp: fresh_list_nil fresh_list_cons fresh_prod fresh_ty)

lemma valid_env_conv: "distinct names \<Longrightarrow> valid (env_conv E names)"
  apply (induction names arbitrary: E)
  apply auto apply (rule_tac v2)
  apply simp apply (rule_tac fresh_env_conv)
  by (simp add: typed_lambda.fresh_list)

fun nclosed where
  "nclosed n (Var i) = (i<n)"
| "nclosed n (App p q) = (nclosed n p \<and> nclosed n q)"
| "nclosed n (MkPair p q) = (nclosed n p \<and> nclosed n q)"
| "nclosed n (Unpair b p) = nclosed n p"
| "nclosed n (Abs p) = nclosed (Suc n) p"


lemma typ_pres:
  "E \<turnstile> p : T \<Longrightarrow> distinct names \<Longrightarrow> nclosed (length names) p \<Longrightarrow> env_conv E names \<turnstile> dB_to_lam names p : typ_conv T"
proof (induction E p T arbitrary: names and names rule:typing.induct)
case (Abs E T p U) 
  define x where "x == fresh_name names"
  (* obtain x::name where x_fresh: "x \<sharp> names" apply atomize_elim apply (rule exists_fresh') by (finite_guess) *)
  have x_fresh: "x \<sharp> names"
    by (simp add: fresh_name x_def)
  have distinct: "distinct (x#names)" using x_fresh `distinct names` by (rule fresh_distinct)
  have nclosed: "nclosed (length (x#names)) p"
    using Abs.prems by simp
  (* have length: "length (x#names) = length (T#E)" using wt_ProcAbs by simp *)
  have IH: "env_conv (E\<langle>0:T\<rangle>) (x#names) \<turnstile> dB_to_lam (x#names) p : typ_conv U"
    using distinct nclosed by (rule Abs.IH)

  have abs: "dB_to_lam names (Abs p) = Lam [x].dB_to_lam (x # names) p"
    apply simp unfolding Let_def x_def by simp

  have x_zip: "x \<sharp> env_conv E names"
    apply (rule fresh_env_conv) using `x \<sharp> names` by assumption

  show ?case
    unfolding abs apply simp
    using x_zip apply (rule TypedLambdaNominal.typing.intros)
    using IH by simp        

next case (Var E i T) 
  have aux: "E i = T \<Longrightarrow> i < length names \<Longrightarrow> (names ! i, typ_conv T) \<in> set (env_conv E names)"
    apply (induction names arbitrary: E i) close
    apply (case_tac i) by auto
  show ?case
    using Var apply simp  
    using valid_env_conv aux by (rule t1)

qed (auto del: typing.intros intro!: typing.intros valid_zip)

lemma length_perm_list [simp]: "length (\<theta> \<bullet> l) = length l"
apply (induction l) by auto



lemma perm_nth: "n < length l \<Longrightarrow> \<theta> \<bullet> l ! n = (\<theta> \<bullet> l) ! n"
apply (induction l arbitrary: n)
using less_Suc_eq_0_disj by auto

lemma rename_dB_to_lam: 
  shows "(\<theta>::name prm) \<bullet> dB_to_lam n p = dB_to_lam (\<theta> \<bullet> n) p"
proof (induction p arbitrary: \<theta> n)
case App thus ?case by auto
next case Var show ?case by (auto simp: perm_nth id_undefined perm_bool lam.inject)
next case (Abs p) 
  define y x where "y == fresh_name n" and "x == fresh_name (\<theta> \<bullet> n)"
  have fresh_x1: "x \<sharp> \<theta> \<bullet> n" unfolding x_def by (rule fresh_name)
  have simp1: "[(x, \<theta> \<bullet> y)] \<bullet> \<theta> \<bullet> n = \<theta> \<bullet> n"
    by (simp add: fresh_bij fresh_x1 perm_fresh_fresh typed_lambda.fresh_name y_def)
  have "\<theta> \<bullet> dB_to_lam n (Abs p) = Lam[(\<theta>\<bullet>y)].dB_to_lam (\<theta>\<bullet>y#\<theta>\<bullet>n) p"
    by (simp add: Let_def y_def[symmetric] Abs.IH) 
  also have "\<dots> = Lam[x].dB_to_lam (x # \<theta> \<bullet> n) p"
    using fresh_x1 
    by (auto simp: simp1 swap_simps Abs.IH lam.inject alpha' fresh_list_cons fresh_atm intro!: fresh_dB_to_lam)
  also have "\<dots> = dB_to_lam (\<theta> \<bullet> n) (Abs p)"
    by (simp add: Let_def x_def)
  finally show ?case by assumption
next case MkPair thus ?case by auto
next case Unpair thus ?case by (auto simp: perm_bool)
qed


lemma lift_translate: 
  "dB_to_lam (x#n) (lift t 0) = dB_to_lam n t"
proof -
  define m where "m == [] :: name list"
  have "dB_to_lam (m@x#n) (lift t (length m)) = dB_to_lam (m@n) t"
  proof (induction t arbitrary: x m)  
  case (Abs t)
    define y where "y == fresh_name (m @ x # n)"
    hence "y \<sharp> (m@x#n)" by (simp add: fresh_name)
    hence "y \<sharp> m" and "y \<sharp> x" and "y \<sharp> n" by (auto simp: fresh_list_cons fresh_list_append)
    define y' where "y' == fresh_name (m @ n)"

    have ym: "[(y, y')] \<bullet> m = m"
      using \<open>y \<sharp> m\<close> fresh_list_append perm_fresh_fresh typed_lambda.fresh_name y'_def by fastforce
    have yn: "[(y, y')] \<bullet> n = n"
      using \<open>y \<sharp> n\<close> fresh_list_append perm_fresh_fresh typed_lambda.fresh_name y'_def by fastforce
    have "dB_to_lam (m @ x # n) (lift (Abs t) (length m)) = Lam [y].dB_to_lam ((y#m)@x#n) (lift t (length (y#m)))"
      by (simp add: y_def[symmetric] Let_def)
    also have "\<dots> = Lam [y].dB_to_lam (y#m @ n) t"
      by (subst Abs, simp)
    also have "\<dots> = Lam [y'].dB_to_lam (y'#m@n) t"
      unfolding lam.inject alpha 
      using `y\<sharp>m` `y\<sharp>n` ym yn
      by (auto simp: rename_dB_to_lam swap_simps append_eqvt fresh_list_cons fresh_list_append fresh_atm intro!: fresh_dB_to_lam)
    also have "\<dots> = dB_to_lam (m @ n) (Abs t)"
      by (simp add: y'_def[symmetric] Let_def)
    finally show ?case by assumption
  qed (auto simp: Let_def nth_append)
  thus ?thesis unfolding m_def by simp
qed


lemma subst_translate: 
  assumes "distinct (x#n)"
  shows "(dB_to_lam (x#n) p)[x::=dB_to_lam n t] = dB_to_lam n (subst p t 0)" (is ?thesis2)
proof -

  define m where "m == [] :: name list"
  have distinct: "distinct (m@x#n)" unfolding m_def using assms by simp
  have "dB_to_lam (m@x#n) p[x::=dB_to_lam (m@n) t] = dB_to_lam (m@n) (subst p t (length m))"
  using distinct proof (induction p arbitrary: m t)
  next case (Abs q) 
    define y where "y == fresh_name (m@x#n)"
    hence "y \<sharp> (m@x#n)" using typed_lambda.fresh_name by auto
    hence "y \<sharp> m" and "y\<sharp>x" and "y\<sharp>n"
      by (auto simp: fresh_list_append fresh_list_cons)
    hence "y \<sharp> (m@n)" by (simp add: fresh_list_append)
    have fresh_y: "y \<sharp> [(x, dB_to_lam (m @ n) t)]"                  
      using `y\<sharp>x` `y\<sharp>(m@n)` by (auto simp: fresh_list_cons fresh_prod fresh_list_nil intro!: fresh_dB_to_lam)
    define y' where "y' == fresh_name (m@n)"
    hence "y' \<sharp> (m@n)" using fresh_name by auto
    hence "y' \<sharp> m" and "y' \<sharp> n"      by (auto simp: fresh_list_append)
    have fresh_y': "y\<noteq>y' \<Longrightarrow> y' \<sharp> dB_to_lam (y # m @ n) (q[lift t 0/Suc (length m)])"
      using `y'\<sharp>(m@n)` by (auto simp: fresh_list_cons fresh_prod fresh_list_nil fresh_atm intro!: fresh_dB_to_lam)

    have IH: "\<And>t. dB_to_lam ((y#m) @ x # n) q[x::=dB_to_lam ((y#m) @ n) t] = dB_to_lam ((y#m) @ n) (q[t/length (y#m)])"
      apply (rule Abs.IH[where m="y#m"]) using Abs.prems `y\<sharp>x` `y\<sharp>m` `y\<sharp>n` fresh_distinct by (auto simp: fresh_atm)
      
    have "dB_to_lam (m @ x # n) (Abs q)[x::=dB_to_lam (m @ n) t] 
       = (Lam [y].dB_to_lam (y#m@x#n) q)[x::=dB_to_lam (m @ n) t]"
       by (simp add: y_def Let_def)
    also have "\<dots> = Lam [y].((dB_to_lam ((y#m)@x#n) q)[x::=dB_to_lam (m @ n) t])"
      apply (subst psubst.simps) using fresh_y by auto
    also have "... = Lam [y].((dB_to_lam ((y#m)@x#n) q)[x::=dB_to_lam ((y#m)@n) (lift t 0)])" by (simp add: lift_translate)
    also have "(dB_to_lam ((y # m) @ x # n) q)[x::=dB_to_lam ((y # m) @ n) (lift t 0)]
             = dB_to_lam ((y#m) @ n) (subst q (lift t 0) (length (y#m)))"
      by (subst IH, simp)
    also have "Lam [y].dB_to_lam ((y#m)@n) (subst q (lift t 0) (length (y#m)))
             = Lam [y'].dB_to_lam (y'#m@n) (subst q (lift t 0) (length (y#m)))"
      apply (subst lam.inject) unfolding alpha'
      apply (cases "y'=y") close
      using `y\<sharp>m` `y'\<sharp>m` `y\<sharp>n` `y'\<sharp>n` fresh_y' by (auto simp: rename_dB_to_lam swap_simps append_eqvt perm_fresh_fresh)
    also have "\<dots> = dB_to_lam (m @ n) (subst (Abs q) t (length m))"
      by (simp add: Let_def y'_def)

    finally show ?case by assumption
  next case (Var i)
    consider (m) "i<length m" | (x) "i=length m" | (n) "i>length m" and "i<length m+length n+1" | (out) "i\<ge>length m+length n+1" apply atomize_elim by auto
    then show ?case proof cases
      case out then show ?thesis by (simp add: forget)
      next case n thus ?thesis apply (auto simp: nth_append)
        by (metis One_nat_def add_diff_cancel_left' add_less_cancel_left assms diff_Suc_1 diff_Suc_eq_diff_pred distinct.simps(2) less_imp_Suc_add nth_mem)
      next case m thus ?thesis apply (auto simp: nth_append)
        using Var.prems by auto
      next case x thus ?thesis by auto
    qed
  qed auto
  thus ?thesis unfolding m_def by auto
qed

fun fresh_names where
  "fresh_names 0 = []"
| "fresh_names (Suc n) = fresh_name (fresh_names n) # fresh_names n"

lemma length_fresh_names: "length (fresh_names i) = i"
  by (induction i, auto)
lemma distinct_fresh_names: "distinct (fresh_names i)"
  apply (induction i) using typed_lambda.fresh_distinct typed_lambda.fresh_name by auto

lemma translate_beta: 
  assumes "beta p q" and "nclosed (length n) p" and "distinct n"
  shows "(dB_to_lam n p) \<longrightarrow>\<^sub>\<beta> (dB_to_lam n q)"
using assms proof (induction arbitrary: n)
case (beta s t) 
  define x where "x == fresh_name n"
  have "x \<sharp> n" unfolding x_def by (rule fresh_name)
  have "dB_to_lam n (Abs s \<degree> t) = lam.App (Lam [x].dB_to_lam (x#n) s) (dB_to_lam n t)"
    by (simp add: Let_def x_def)
  also have "\<dots> \<longrightarrow>\<^sub>\<beta> (dB_to_lam (x#n) s) [ x ::= dB_to_lam n t ]"
    apply (rule b4) using `x\<sharp>n` by (rule fresh_dB_to_lam)
  also have "\<dots> = dB_to_lam n (s[t/0])"
    apply (subst subst_translate)
     using beta.prems `x\<sharp>n` fresh_distinct by (auto simp: fresh_atm)
  finally show ?case by assumption
next case appL thus ?case by auto
next case appR thus ?case by auto
next case abs thus ?case 
  apply auto by (metis b3 fresh_name length_Cons fresh_distinct)
next case pairL thus ?case by auto
next case pairR thus ?case by auto
next case unpair thus ?case by auto
next case fst thus ?case by auto
next case snd thus ?case by auto
qed

lemma nclosed_mono: "n \<le> m \<Longrightarrow> nclosed n p \<Longrightarrow> nclosed m p" 
  apply (induction p arbitrary:n m) apply auto by blast
lemma nclosed_lift: assumes "nclosed n t" shows "nclosed (Suc n) (lift t i)"
  using assms apply (induction t arbitrary: n i) by auto
lemma nclosed_subst: assumes "nclosed (Suc n) s" and "nclosed n t" shows "nclosed n (s[t::dB/0])"
proof -
  define i where "i == 0::nat"
  hence i_n: "i \<le> n" by simp
  show ?thesis
    unfolding i_def[symmetric] using assms i_n
    apply (induction s arbitrary: i n t) by (auto simp: subst_Var nclosed_lift)
qed
lemma nclosed_pres: "p \<rightarrow>\<^sub>\<beta> p' \<Longrightarrow> nclosed n p \<Longrightarrow> nclosed n p'"
  apply (induction arbitrary:n rule:beta.induct) using nclosed_subst by auto

lemma type_implies_termi:
  assumes wt: "typing E p T" shows "termip beta p"
proof -
  obtain i where nclosed: "nclosed i p" apply atomize_elim apply (induction p) using nclosed_mono apply auto
    apply (tactic {* distinct_subgoals_tac *})
   using nat_le_linear close blast 
  using Suc_n_not_le_n nat_le_linear by blast
  define n where "n == fresh_names i"
  have distinct_n: "distinct n"
    unfolding n_def by (rule distinct_fresh_names) 
  have length_n: "length n = i"
    by (simp add: n_def typed_lambda.length_fresh_names)

  define lam_p where "lam_p == dB_to_lam n p"
  have sn: "SN lam_p"
    unfolding lam_p_def
    apply (rule typing_implies_SN)
    apply (rule typ_pres)
      close (fact wt) close (fact distinct_n)
    using nclosed length_n by simp


  from sn lam_p_def[THEN meta_eq_to_obj_eq] nclosed 
  show "termip beta p"
  proof (induction arbitrary: p)
  case (SN_intro t)
    have termip_succ: "termip beta p'" if p': "p \<rightarrow>\<^sub>\<beta> p'" for p'
    proof -
      have succ: "t \<longrightarrow>\<^sub>\<beta> dB_to_lam n p'"
        unfolding SN_intro apply (rule translate_beta)
         close (fact p') using SN_intro length_n distinct_n by auto
      have ncl: "nclosed i p'" using p' SN_intro.prems(2) by (rule nclosed_pres)
      show ?thesis
        apply (rule SN_intro.IH) using succ ncl by auto
    qed
    show ?case
      apply (rule accpI) using termip_succ by blast
  qed
qed



end

end
