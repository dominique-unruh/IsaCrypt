theory TypedLambdaNominal
imports "HOL-Nominal.Nominal"
begin

text {* 
  Provides useful definitions for reasoning
  with lambda-terms. 
*}

atom_decl name

nominal_datatype lam = 
    Var "name"
  | App "lam" "lam"
  | Lam "\<guillemotleft>name\<guillemotright>lam" ("Lam [_]._" [100,100] 100)
  | MkPair lam lam
  | Unpair bool lam 


text {* The depth of a lambda-term. *}

nominal_primrec
  depth :: "lam \<Rightarrow> nat"
where
  "depth (Var x) = 1"
| "depth (App t1 t2) = (max (depth t1) (depth t2)) + 1"
| "depth (MkPair t1 t2) = (max (depth t1) (depth t2)) + 1"
| "depth (Unpair b t) = depth t + 1"
| "depth (Lam [a].t) = depth t + 1"
  apply(finite_guess)+
  apply(rule TrueI)+
  apply(simp add: fresh_nat)
  apply(fresh_guess)+
  done

text {* 
  The free variables of a lambda-term. A complication in this
  function arises from the fact that it returns a name set, which 
  is not a finitely supported type. Therefore we have to prove 
  the invariant that frees always returns a finite set of names. 
*}

nominal_primrec (invariant: "\<lambda>s::name set. finite s")
  frees :: "lam \<Rightarrow> name set"
where
  "frees (Var a) = {a}"
| "frees (App t1 t2) = (frees t1) \<union> (frees t2)"
| "frees (MkPair t1 t2) = (frees t1) \<union> (frees t2)"
| "frees (Unpair b t) = frees t"
| "frees (Lam [a].t) = (frees t) - {a}"
apply(finite_guess)+
apply(simp)+ 
apply(simp add: fresh_def)
apply(simp add: supp_of_fin_sets[OF pt_name_inst, OF at_name_inst, OF fs_at_inst[OF at_name_inst]])
apply(simp add: supp_atm)
apply(blast)
apply(fresh_guess)+
done

text {* 
  We can avoid the definition of frees by
  using the build in notion of support.
*}

find_theorems "supp (_::bool)"
lemma frees_equals_support:
  shows "frees t = supp t"
by (nominal_induct t rule: lam.strong_induct)
   (simp_all add: lam.supp supp_atm supp_bool abs_supp)

text {* Parallel and single capture-avoiding substitution. *}

fun
  lookup :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam"   
where
  "lookup [] x        = Var x"
| "lookup ((y,e)#\<theta>) x = (if x=y then e else lookup \<theta> x)"

lemma lookup_eqvt[eqvt]:
  fixes pi::"name prm"
  and   \<theta>::"(name\<times>lam) list"
  and   X::"name"
  shows "pi\<bullet>(lookup \<theta> X) = lookup (pi\<bullet>\<theta>) (pi\<bullet>X)"
by (induct \<theta>) (auto simp add: eqvts)
 
nominal_primrec
  psubst :: "(name\<times>lam) list \<Rightarrow> lam \<Rightarrow> lam"  ("_<_>" [95,95] 105)
where
  "\<theta><(Var x)> = (lookup \<theta> x)"
| "\<theta><(App e\<^sub>1 e\<^sub>2)> = App (\<theta><e\<^sub>1>) (\<theta><e\<^sub>2>)"
| "\<theta><(MkPair e\<^sub>1 e\<^sub>2)> = MkPair (\<theta><e\<^sub>1>) (\<theta><e\<^sub>2>)"
| "\<theta><(Unpair b e)> = Unpair b (\<theta><e>)"
| "x\<sharp>\<theta> \<Longrightarrow> \<theta><(Lam [x].e)> = Lam [x].(\<theta><e>)"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: abs_fresh)+
apply(fresh_guess)+
done

lemma psubst_eqvt[eqvt]:
  fixes pi::"name prm" 
  and   t::"lam"
  shows "pi\<bullet>(\<theta><t>) = (pi\<bullet>\<theta>)<(pi\<bullet>t)>"
by (nominal_induct t avoiding: \<theta> rule: lam.strong_induct)
   (simp_all add: eqvts fresh_bij)

abbreviation 
  subst :: "lam \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> lam" ("_[_::=_]" [100,100,100] 100)
where 
  "t[x::=t']  \<equiv> ([(x,t')])<t>" 

lemma subst[simp]:
  shows "(Var x)[y::=t'] = (if x=y then t' else (Var x))"
  and   "(App t1 t2)[y::=t'] = App (t1[y::=t']) (t2[y::=t'])"
  and   "(MkPair t1 t2)[y::=t'] = MkPair (t1[y::=t']) (t2[y::=t'])"
  and   "(Unpair b t)[y::=t'] = Unpair b (t[y::=t'])"
  and   "x\<sharp>(y,t') \<Longrightarrow> (Lam [x].t)[y::=t'] = Lam [x].(t[y::=t'])"
by (simp_all add: fresh_list_cons fresh_list_nil)

lemma subst_supp: 
  shows "supp(t1[a::=t2]) \<subseteq> (((supp(t1)-{a})\<union>supp(t2))::name set)"
apply(nominal_induct t1 avoiding: a t2 rule: lam.strong_induct)
apply(auto simp add: lam.supp supp_atm fresh_prod abs_supp supp_bool)
apply(blast)+
done

(* 
text {* 
  Contexts - lambda-terms with a single hole.
  Note that the lambda case in contexts does not bind a 
  name, even if we introduce the notation [_]._ for CLam.
*}
nominal_datatype clam = 
    Hole ("\<box>" 1000)  
  | CAppL "clam" "lam"
  | CAppR "lam" "clam" 
  | CMkPairL "clam" "lam"
  | CMkPairR "lam" "clam" 
  | CUnpair bool clam
  | CLam "name" "clam"  ("CLam [_]._" [100,100] 100) 

text {* Filling a lambda-term into a context. *}

nominal_primrec
  filling :: "clam \<Rightarrow> lam \<Rightarrow> lam" ("_\<lbrakk>_\<rbrakk>" [100,100] 100)
where
  "\<box>\<lbrakk>t\<rbrakk> = t"
| "(CAppL E t')\<lbrakk>t\<rbrakk> = App (E\<lbrakk>t\<rbrakk>) t'"
| "(CAppR t' E)\<lbrakk>t\<rbrakk> = App t' (E\<lbrakk>t\<rbrakk>)"
| "(CMkPairL E t')\<lbrakk>t\<rbrakk> = MkPair (E\<lbrakk>t\<rbrakk>) t'"
| "(CMkPairR t' E)\<lbrakk>t\<rbrakk> = MkPair t' (E\<lbrakk>t\<rbrakk>)"
| "(CUnpair b E)\<lbrakk>t\<rbrakk> = Unpair b (E\<lbrakk>t\<rbrakk>)"
| "(CLam [x].E)\<lbrakk>t\<rbrakk> = Lam [x].(E\<lbrakk>t\<rbrakk>)" 
by (rule TrueI)+

text {* Composition of two contexts *}

nominal_primrec
 clam_compose :: "clam \<Rightarrow> clam \<Rightarrow> clam" ("_ \<circ> _" [100,100] 100)
where
  "\<box> \<circ> E' = E'"
| "(CAppL E t') \<circ> E' = CAppL (E \<circ> E') t'"
| "(CAppR t' E) \<circ> E' = CAppR t' (E \<circ> E')"
| "(CMkPairL E t') \<circ> E' = CMkPairL (E \<circ> E') t'"
| "(CMkPairR t' E) \<circ> E' = CMkPairR t' (E \<circ> E')"
| "(CUnpair b E) \<circ> E' = CUnpair b (E \<circ> E')"
| "(CLam [x].E) \<circ> E' = CLam [x].(E \<circ> E')"
by (rule TrueI)+
  
lemma clam_compose:
  shows "(E1 \<circ> E2)\<lbrakk>t\<rbrakk> = E1\<lbrakk>E2\<lbrakk>t\<rbrakk>\<rbrakk>"
by (induct E1 rule: clam.induct) (auto) *)

text {* Strong Normalisation proof from the Proofs and Types book *}
text {* Based on HOL/Nominal/Examples/SN.thy, extended to product types by Dominique Unruh *}

section {* Beta Reduction *}                                                            

lemma subst_rename: 
  assumes a: "c\<sharp>t1"
  shows "t1[a::=t2] = ([(c,a)]\<bullet>t1)[c::=t2]"
using a
by (nominal_induct t1 avoiding: a c t2 rule: lam.strong_induct)
   (auto simp add: calc_atm fresh_atm abs_fresh perm_bool)

lemma forget: 
  assumes a: "a\<sharp>t1"
  shows "t1[a::=t2] = t1"
  using a
by (nominal_induct t1 avoiding: a t2 rule: lam.strong_induct)
   (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact: 
  fixes a::"name"
  assumes a: "a\<sharp>t1" "a\<sharp>t2"
  shows "a\<sharp>t1[b::=t2]"
using a
by (nominal_induct t1 avoiding: a b t2 rule: lam.strong_induct)
   (auto simp add: abs_fresh fresh_atm)

lemma fresh_fact': 
  fixes a::"name"
  assumes a: "a\<sharp>t2"
  shows "a\<sharp>t1[a::=t2]"
using a 
by (nominal_induct t1 avoiding: a t2 rule: lam.strong_induct)
   (auto simp add: abs_fresh fresh_atm fresh_bool)

lemma subst_lemma:  
  assumes a: "x\<noteq>y"
  and     b: "x\<sharp>L"
  shows "M[x::=N][y::=L] = M[y::=L][x::=N[y::=L]]"
using a b
by (nominal_induct M avoiding: x y N L rule: lam.strong_induct)
   (auto simp add: fresh_fact forget)

lemma id_subs: 
  shows "t[x::=Var x] = t"
  by (nominal_induct t avoiding: x rule: lam.strong_induct)
     (simp_all add: fresh_atm)

lemma lookup_fresh:
  fixes z::"name"
  assumes "z\<sharp>\<theta>" "z\<sharp>x"
  shows "z\<sharp> lookup \<theta> x"
using assms 
by (induct rule: lookup.induct) (auto simp add: fresh_list_cons)

lemma lookup_fresh':
  assumes "z\<sharp>\<theta>"
  shows "lookup \<theta> z = Var z"
using assms 
by (induct rule: lookup.induct)
   (auto simp add: fresh_list_cons fresh_prod fresh_atm)

lemma psubst_subst:
  assumes h:"c\<sharp>\<theta>"
  shows "(\<theta><t>)[c::=s] = ((c,s)#\<theta>)<t>"
  using h
by (nominal_induct t avoiding: \<theta> c s rule: lam.strong_induct)
   (auto simp add: fresh_list_cons fresh_atm forget lookup_fresh lookup_fresh')
 
inductive 
  Beta :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<longrightarrow>\<^sub>\<beta> _" [80,80] 80)
where
  b1[intro!]: "s1 \<longrightarrow>\<^sub>\<beta> s2 \<Longrightarrow> App s1 t \<longrightarrow>\<^sub>\<beta> App s2 t"
| b2[intro!]: "s1 \<longrightarrow>\<^sub>\<beta> s2 \<Longrightarrow> App t s1 \<longrightarrow>\<^sub>\<beta> App t s2"
| b3[intro!]: "s1 \<longrightarrow>\<^sub>\<beta> s2 \<Longrightarrow> Lam [a].s1 \<longrightarrow>\<^sub>\<beta> Lam [a].s2"
| b4[intro!]: "a\<sharp>s2 \<Longrightarrow> App (Lam [a].s1) s2\<longrightarrow>\<^sub>\<beta> (s1[a::=s2])"
| b5[intro!]: "s1 \<longrightarrow>\<^sub>\<beta> s2 \<Longrightarrow> MkPair s1 t \<longrightarrow>\<^sub>\<beta> MkPair s2 t"
| b6[intro!]: "s1 \<longrightarrow>\<^sub>\<beta> s2 \<Longrightarrow> MkPair t s1 \<longrightarrow>\<^sub>\<beta> MkPair t s2"
| b7[intro!]: "s1 \<longrightarrow>\<^sub>\<beta> s2 \<Longrightarrow> Unpair b s1 \<longrightarrow>\<^sub>\<beta> Unpair b s2"
| b8[intro!]: "Unpair True (MkPair s1 s2) \<longrightarrow>\<^sub>\<beta> s1"
| b9[intro!]: "Unpair False (MkPair s1 s2) \<longrightarrow>\<^sub>\<beta> s2"     

equivariance Beta

nominal_inductive Beta
  by (simp_all add: abs_fresh fresh_fact')

lemma beta_preserves_fresh: 
  fixes a::"name"
  assumes a: "t\<longrightarrow>\<^sub>\<beta> s"
  shows "a\<sharp>t \<Longrightarrow> a\<sharp>s"
using a
apply(nominal_induct t s avoiding: a rule: Beta.strong_induct)
apply(auto simp add: abs_fresh fresh_fact fresh_atm)
done

lemma beta_abs: 
  assumes a: "Lam [a].t \<longrightarrow>\<^sub>\<beta> t'" 
  shows "\<exists>t''. t'=Lam [a].t'' \<and> t \<longrightarrow>\<^sub>\<beta> t''"
proof -
  have "a\<sharp>Lam [a].t" by (simp add: abs_fresh)
  with a have "a\<sharp>t'" by (simp add: beta_preserves_fresh)
  with a show ?thesis
    by (cases rule: Beta.strong_cases[where a="a" and aa="a"])
       (auto simp add: lam.inject abs_fresh alpha)
qed

lemma beta_subst: 
  assumes a: "M \<longrightarrow>\<^sub>\<beta> M'"
  shows "M[x::=N] \<longrightarrow>\<^sub>\<beta> M'[x::=N]" 
using a
by (nominal_induct M M' avoiding: x N rule: Beta.strong_induct)
   (auto simp add: fresh_atm subst_lemma fresh_fact)

section {* types *}

nominal_datatype ty =
    TVar "nat"
  | TArr "ty" "ty" (infix "\<rightarrow>" 200)
  | TPair ty ty

lemma fresh_ty:
  fixes a :: "name"
  and   \<tau>  :: "ty"
  shows "a\<sharp>\<tau>"
by (nominal_induct \<tau> rule: ty.strong_induct)
   (auto simp add: fresh_nat)

(* valid contexts *)

inductive 
  valid :: "(name\<times>ty) list \<Rightarrow> bool"
where
  v1[intro]: "valid []"
| v2[intro]: "\<lbrakk>valid \<Gamma>;a\<sharp>\<Gamma>\<rbrakk>\<Longrightarrow> valid ((a,\<sigma>)#\<Gamma>)"

equivariance valid 

(* typing judgements *)

lemma fresh_context: 
  fixes  \<Gamma> :: "(name\<times>ty)list"
  and    a :: "name"
  assumes a: "a\<sharp>\<Gamma>"
  shows "\<not>(\<exists>\<tau>::ty. (a,\<tau>)\<in>set \<Gamma>)"
using a
by (induct \<Gamma>)
   (auto simp add: fresh_prod fresh_list_cons fresh_atm)

inductive 
  typing :: "(name\<times>ty) list\<Rightarrow>lam\<Rightarrow>ty\<Rightarrow>bool" ("_ \<turnstile> _ : _" [60,60,60] 60)
where
  t1[intro]: "\<lbrakk>valid \<Gamma>; (a,\<tau>)\<in>set \<Gamma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Var a : \<tau>"
| t2[intro]: "\<lbrakk>\<Gamma> \<turnstile> t1 : \<tau>\<rightarrow>\<sigma>; \<Gamma> \<turnstile> t2 : \<tau>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> App t1 t2 : \<sigma>"
| t3[intro]: "\<lbrakk>a\<sharp>\<Gamma>;((a,\<tau>)#\<Gamma>) \<turnstile> t : \<sigma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> Lam [a].t : \<tau>\<rightarrow>\<sigma>"
| t4[intro]: "\<lbrakk>\<Gamma> \<turnstile> t1 : \<tau>; \<Gamma> \<turnstile> t2 : \<sigma>\<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> MkPair t1 t2 : TPair \<tau> \<sigma>"
| t5[intro]: "\<Gamma> \<turnstile> t : TPair \<tau> \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> Unpair True t : \<tau>"
| t6[intro]: "\<Gamma> \<turnstile> t : TPair \<tau> \<sigma> \<Longrightarrow> \<Gamma> \<turnstile> Unpair False t : \<sigma>"

equivariance typing

nominal_inductive typing
  by (simp_all add: abs_fresh fresh_ty)

subsection {* a fact about beta *}

definition "NORMAL" :: "lam \<Rightarrow> bool" where
  "NORMAL t \<equiv> \<not>(\<exists>t'. t\<longrightarrow>\<^sub>\<beta> t')"

lemma NORMAL_Var:
  shows "NORMAL (Var a)"
proof -
  { assume "\<exists>t'. (Var a) \<longrightarrow>\<^sub>\<beta> t'"
    then obtain t' where "(Var a) \<longrightarrow>\<^sub>\<beta> t'" by blast
    hence False by (cases) (auto) 
  }
  thus "NORMAL (Var a)" by (auto simp add: NORMAL_def)
qed

text {* Inductive version of Strong Normalisation *}
inductive 
  SN :: "lam \<Rightarrow> bool"
where
  SN_intro: "(\<And>t'. t \<longrightarrow>\<^sub>\<beta> t' \<Longrightarrow> SN t') \<Longrightarrow> SN t"

lemma SN_preserved: 
  assumes a: "SN t1" "t1\<longrightarrow>\<^sub>\<beta> t2"
  shows "SN t2"
using a 
by (cases) (auto)

lemma double_SN_aux:
  assumes a: "SN a"
  and b: "SN b"
  and hyp: "\<And>x z.
    \<lbrakk>\<And>y. x \<longrightarrow>\<^sub>\<beta> y \<Longrightarrow> SN y; \<And>y. x \<longrightarrow>\<^sub>\<beta> y \<Longrightarrow> P y z;
     \<And>u. z \<longrightarrow>\<^sub>\<beta> u \<Longrightarrow> SN u; \<And>u. z \<longrightarrow>\<^sub>\<beta> u \<Longrightarrow> P x u\<rbrakk> \<Longrightarrow> P x z"
  shows "P a b"
proof -
  from a
  have r: "\<And>b. SN b \<Longrightarrow> P a b"
  proof (induct a rule: SN.induct)
    case (SN_intro x)
    note SNI' = SN_intro
    have "SN b" by fact
    thus ?case
    proof (induct b rule: SN.induct)
      case (SN_intro y)
      show ?case
        apply (rule hyp)
        apply (erule SNI')
        apply (erule SNI')
        apply (rule SN.SN_intro)
        apply (erule SN_intro)+
        done
    qed
  qed
  from b show ?thesis by (rule r)
qed

lemma double_SN[consumes 2]:
  assumes a: "SN a"
  and     b: "SN b" 
  and     c: "\<And>x z. \<lbrakk>\<And>y. x \<longrightarrow>\<^sub>\<beta> y \<Longrightarrow> P y z; \<And>u. z \<longrightarrow>\<^sub>\<beta> u \<Longrightarrow> P x u\<rbrakk> \<Longrightarrow> P x z"
  shows "P a b"
using a b c
apply(rule_tac double_SN_aux)
apply(assumption)+
apply(blast)
done

section {* Candidates *}

nominal_primrec
  RED :: "ty \<Rightarrow> lam set"
where
  "RED (TVar X) = {t. SN(t)}"
| "RED (\<tau>\<rightarrow>\<sigma>) =   {t. \<forall>u. (u\<in>RED \<tau> \<longrightarrow> (App t u)\<in>RED \<sigma>)}"
| "RED (TPair \<tau> \<sigma>) = {t. Unpair True t \<in> RED \<tau> \<and> Unpair False t \<in> RED \<sigma>}"
by (rule TrueI)+

text {* neutral terms *}
definition NEUT :: "lam \<Rightarrow> bool" where
  "NEUT t \<equiv> (\<exists>a. t = Var a) \<or> (\<exists>t1 t2. t = App t1 t2) \<or> (\<exists>b u. t = Unpair b u)"

(* a slight hack to get the first element of applications *)
(* this is needed to get (SN t) from SN (App t s)         *) 
inductive 
  FST :: "lam\<Rightarrow>lam\<Rightarrow>bool" (" _ \<guillemotright> _" [80,80] 80)
where
  fst[intro!]:  "(App t s) \<guillemotright> t"

nominal_primrec
  fst_app_aux::"lam\<Rightarrow>lam option"
where
  "fst_app_aux (Var a)     = None"
| "fst_app_aux (App t1 t2) = Some t1"
| "fst_app_aux (Lam [x].t) = None"
| "fst_app_aux (MkPair t1 t2) = None"
| "fst_app_aux (Unpair b t) = None"
apply(finite_guess)+
apply(rule TrueI)+
apply(simp add: fresh_none)
apply(fresh_guess)+
done

definition
  fst_app_def[simp]: "fst_app t = the (fst_app_aux t)"

lemma SN_of_FST_of_App: 
  assumes a: "SN (App t s)"
  shows "SN (fst_app (App t s))"
using a
proof - 
  from a have "\<forall>z. (App t s \<guillemotright> z) \<longrightarrow> SN z"
    by (induct rule: SN.induct)
       (blast elim: FST.cases intro: SN_intro)
  then have "SN t" by blast
  then show "SN (fst_app (App t s))" by simp
qed

lemma SN_of_Unpair_arg:
  assumes a: "SN (Unpair True t)"
  shows "SN t"
proof -
  define u where "u \<equiv> Unpair True t"
  have "SN u" using a unfolding u_def by simp
  have u_def': "u = Unpair True t" using u_def by simp
  show "SN t"
    using `SN u` u_def' apply (induct arbitrary: t) apply (rule SN.intros) by auto
qed    

section {* Candidates *}

definition "CR1" :: "ty \<Rightarrow> bool" where
  "CR1 \<tau> \<equiv> \<forall>t. (t\<in>RED \<tau> \<longrightarrow> SN t)"

definition "CR2" :: "ty \<Rightarrow> bool" where
  "CR2 \<tau> \<equiv> \<forall>t t'. (t\<in>RED \<tau> \<and> t \<longrightarrow>\<^sub>\<beta> t') \<longrightarrow> t'\<in>RED \<tau>"

definition "CR3_RED" :: "lam \<Rightarrow> ty \<Rightarrow> bool" where
  "CR3_RED t \<tau> \<equiv> \<forall>t'. t\<longrightarrow>\<^sub>\<beta> t' \<longrightarrow>  t'\<in>RED \<tau>" 

definition "CR3" :: "ty \<Rightarrow> bool" where
  "CR3 \<tau> \<equiv> \<forall>t. (NEUT t \<and> CR3_RED t \<tau>) \<longrightarrow> t\<in>RED \<tau>"
   
definition "CR4" :: "ty \<Rightarrow> bool" where
  "CR4 \<tau> \<equiv> \<forall>t. (NEUT t \<and> NORMAL t) \<longrightarrow>t\<in>RED \<tau>"

lemma CR3_implies_CR4: 
  assumes a: "CR3 \<tau>" 
  shows "CR4 \<tau>"
using a by (auto simp add: CR3_def CR3_RED_def CR4_def NORMAL_def)

(* sub_induction in the arrow-type case for the next proof *) 
lemma sub_induction: 
  assumes a: "SN(u)"
  and     b: "u\<in>RED \<tau>"
  and     c1: "NEUT t"
  and     c2: "CR2 \<tau>"
  and     c3: "CR3 \<sigma>"
  and     c4: "CR3_RED t (\<tau>\<rightarrow>\<sigma>)"
  shows "(App t u)\<in>RED \<sigma>"
using a b
proof (induct)
  fix u
  assume as: "u\<in>RED \<tau>"
  assume ih: " \<And>u'. \<lbrakk>u \<longrightarrow>\<^sub>\<beta> u'; u' \<in> RED \<tau>\<rbrakk> \<Longrightarrow> App t u' \<in> RED \<sigma>"
  have "NEUT (App t u)" using c1 by (auto simp add: NEUT_def)
  moreover
  have "CR3_RED (App t u) \<sigma>" unfolding CR3_RED_def
  proof (intro strip)
    fix r
    assume red: "App t u \<longrightarrow>\<^sub>\<beta> r"
    moreover
    { assume "\<exists>t'. t \<longrightarrow>\<^sub>\<beta> t' \<and> r = App t' u"
      then obtain t' where a1: "t \<longrightarrow>\<^sub>\<beta> t'" and a2: "r = App t' u" by blast
      have "t'\<in>RED (\<tau>\<rightarrow>\<sigma>)" using c4 a1 by (simp add: CR3_RED_def)
      then have "App t' u\<in>RED \<sigma>" using as by simp
      then have "r\<in>RED \<sigma>" using a2 by simp
    }
    moreover
    { assume "\<exists>u'. u \<longrightarrow>\<^sub>\<beta> u' \<and> r = App t u'"
      then obtain u' where b1: "u \<longrightarrow>\<^sub>\<beta> u'" and b2: "r = App t u'" by blast
      have "u'\<in>RED \<tau>" using as b1 c2 by (auto simp add: CR2_def)
      with ih have "App t u' \<in> RED \<sigma>" using b1 by simp
      then have "r\<in>RED \<sigma>" using b2 by simp
    }
    moreover
    { assume "\<exists>x t'. t = Lam [x].t'"
      then obtain x t' where "t = Lam [x].t'" by blast
      then have "NEUT (Lam [x].t')" using c1 by simp
      then have "False" by (simp add: NEUT_def)
      then have "r\<in>RED \<sigma>" by simp
    }
    ultimately show "r \<in> RED \<sigma>" by (cases) (auto simp add: lam.inject)
  qed
  ultimately show "App t u \<in> RED \<sigma>" using c3 by (simp add: CR3_def)
qed 

text {* properties of the candiadates *}
lemma RED_props: 
  shows "CR1 \<tau>" and "CR2 \<tau>" and "CR3 \<tau>"
proof (nominal_induct \<tau> rule: ty.strong_induct)
  case (TVar a)
  { case 1 show "CR1 (TVar a)" by (simp add: CR1_def)
  next
    case 2 show "CR2 (TVar a)" by (auto intro: SN_preserved simp add: CR2_def)
  next
    case 3 show "CR3 (TVar a)" by (auto intro: SN_intro simp add: CR3_def CR3_RED_def)
  }
next
  case (TArr \<tau>1 \<tau>2)
  { case 1
    have ih_CR3_\<tau>1: "CR3 \<tau>1" by fact
    have ih_CR1_\<tau>2: "CR1 \<tau>2" by fact
    have "\<And>t. t \<in> RED (\<tau>1 \<rightarrow> \<tau>2) \<Longrightarrow> SN t" 
    proof - 
      fix t
      assume "t \<in> RED (\<tau>1 \<rightarrow> \<tau>2)"
      then have a: "\<forall>u. u \<in> RED \<tau>1 \<longrightarrow> App t u \<in> RED \<tau>2" by simp
      from ih_CR3_\<tau>1 have "CR4 \<tau>1" by (simp add: CR3_implies_CR4) 
      moreover
      fix a have "NEUT (Var a)" by (force simp add: NEUT_def)
      moreover
      have "NORMAL (Var a)" by (rule NORMAL_Var)
      ultimately have "(Var a)\<in> RED \<tau>1" by (simp add: CR4_def)
      with a have "App t (Var a) \<in> RED \<tau>2" by simp
      hence "SN (App t (Var a))" using ih_CR1_\<tau>2 by (simp add: CR1_def)
      thus "SN t" by (auto dest: SN_of_FST_of_App)
    qed
    then show "CR1 (\<tau>1 \<rightarrow> \<tau>2)" unfolding CR1_def by simp
  next
    case 2
    have ih_CR2_\<tau>2: "CR2 \<tau>2" by fact
    then show "CR2 (\<tau>1 \<rightarrow> \<tau>2)" unfolding CR2_def by auto 
  next
    case 3
    have ih_CR1_\<tau>1: "CR1 \<tau>1" by fact
    have ih_CR2_\<tau>1: "CR2 \<tau>1" by fact
    have ih_CR3_\<tau>2: "CR3 \<tau>2" by fact
    show "CR3 (\<tau>1 \<rightarrow> \<tau>2)" unfolding CR3_def
    proof (simp, intro strip)
      fix t u
      assume a1: "u \<in> RED \<tau>1"
      assume a2: "NEUT t \<and> CR3_RED t (\<tau>1 \<rightarrow> \<tau>2)"
      have "SN(u)" using a1 ih_CR1_\<tau>1 by (simp add: CR1_def)
      then show "(App t u)\<in>RED \<tau>2" using ih_CR2_\<tau>1 ih_CR3_\<tau>2 a1 a2 by (blast intro: sub_induction)
    qed
  }
case (TPair \<sigma> \<tau>)
  { case 1
    show ?case 
    proof (unfold CR1_def, rule allI, rule impI)
      fix t assume "t \<in> RED (TPair \<sigma> \<tau>)"
      hence "Unpair True t \<in> RED \<sigma>" by simp 
      hence "SN (Unpair True t)"
        using CR1_def `CR1 \<sigma>` by auto
      thus "SN t"
        by (rule SN_of_Unpair_arg)
    qed
  next
    case 2
    show ?case
    proof (unfold CR2_def, (rule allI)+, (rule impI), erule conjE)
      fix t t' assume tred: "t \<in> RED (TPair \<sigma> \<tau>)" and beta: "t \<longrightarrow>\<^sub>\<beta> t'"
      have t1beta: "Unpair True t \<longrightarrow>\<^sub>\<beta> Unpair True t'"
       and t2beta: "Unpair False t \<longrightarrow>\<^sub>\<beta> Unpair False t'"
        using beta by (simp_all add: b7 b8)
      have "Unpair True t \<in> RED \<sigma>" and "Unpair False t \<in> RED \<tau>"
        using tred by auto
      hence "Unpair True t' \<in> RED \<sigma>" and "Unpair False t' \<in> RED \<tau>" 
        using CR2_def `CR2 \<sigma>` `CR2 \<tau>` t1beta t2beta by auto
      thus "t' \<in> RED (TPair \<sigma> \<tau>)" by simp
    qed
  next
    case 3
    show ?case
    proof (unfold CR3_def, rule allI, rule impI, erule conjE)
      fix t assume "NEUT t" assume "CR3_RED t (TPair \<sigma> \<tau>)"
      hence t_succ_red: "\<And>t'. t \<longrightarrow>\<^sub>\<beta> t' \<Longrightarrow> t' \<in> RED (TPair \<sigma> \<tau>)" unfolding CR3_RED_def by simp
      have "CR3_RED (Unpair True t) \<sigma>"
      proof (unfold CR3_RED_def, rule allI, rule impI)
        fix t' assume fst_t_beta: "Unpair True t \<longrightarrow>\<^sub>\<beta> t'"
        obtain u where "t' = Unpair True u" and "t \<longrightarrow>\<^sub>\<beta> u"
          apply atomize_elim using fst_t_beta apply cases
          using NEUT_def \<open>NEUT t\<close> by (auto simp: lam.inject)  
        thus "t' \<in> RED \<sigma>"
          using t_succ_red by auto
      qed
      moreover have "NEUT (Unpair True t)" unfolding NEUT_def by auto
      ultimately have red_fst: "Unpair True t \<in> RED \<sigma>"
        using `CR3 \<sigma>`[unfolded CR3_def] by auto
      have "CR3_RED (Unpair False t) \<tau>"
      proof (unfold CR3_RED_def, rule allI, rule impI)
        fix t' assume snd_t_beta: "Unpair False t \<longrightarrow>\<^sub>\<beta> t'"
        obtain u where "t' = Unpair False u" and "t \<longrightarrow>\<^sub>\<beta> u"
          apply atomize_elim using snd_t_beta apply cases
          using NEUT_def \<open>NEUT t\<close> by (auto simp: lam.inject)  
        thus "t' \<in> RED \<tau>"
          using t_succ_red by auto
      qed
      moreover have "NEUT (Unpair False t)" unfolding NEUT_def by auto
      ultimately have red_snd: "Unpair False t \<in> RED \<tau>"
        using `CR3 \<tau>`[unfolded CR3_def] by auto
      from red_fst red_snd show "t \<in> RED (TPair \<sigma> \<tau>)" by auto
    qed
  }
qed
   
text {* 
  the next lemma not as simple as on paper, probably because of 
  the stronger double_SN induction 
*} 
lemma abs_RED: 
  assumes asm: "\<forall>s\<in>RED \<tau>. t[x::=s]\<in>RED \<sigma>"
  shows "Lam [x].t\<in>RED (\<tau>\<rightarrow>\<sigma>)"
proof -
  have b1: "SN t" 
  proof -
    have "Var x\<in>RED \<tau>"
    proof -
      have "CR4 \<tau>" by (simp add: RED_props CR3_implies_CR4)
      moreover
      have "NEUT (Var x)" by (auto simp add: NEUT_def)
      moreover
      have "NORMAL (Var x)" by (auto elim: Beta.cases simp add: NORMAL_def)
      ultimately show "Var x\<in>RED \<tau>" by (simp add: CR4_def)
    qed
    then have "t[x::=Var x]\<in>RED \<sigma>" using asm by simp
    then have "t\<in>RED \<sigma>" by (simp add: id_subs)
    moreover 
    have "CR1 \<sigma>" by (simp add: RED_props)
    ultimately show "SN t" by (simp add: CR1_def)
  qed
  show "Lam [x].t\<in>RED (\<tau>\<rightarrow>\<sigma>)"
  proof (simp, intro strip)
    fix u
    assume b2: "u\<in>RED \<tau>"
    then have b3: "SN u" using RED_props by (auto simp add: CR1_def)
    show "App (Lam [x].t) u \<in> RED \<sigma>" using b1 b3 b2 asm
    proof(induct t u rule: double_SN)
      fix t u
      assume ih1: "\<And>t'.  \<lbrakk>t \<longrightarrow>\<^sub>\<beta> t'; u\<in>RED \<tau>; \<forall>s\<in>RED \<tau>. t'[x::=s]\<in>RED \<sigma>\<rbrakk> \<Longrightarrow> App (Lam [x].t') u \<in> RED \<sigma>" 
      assume ih2: "\<And>u'.  \<lbrakk>u \<longrightarrow>\<^sub>\<beta> u'; u'\<in>RED \<tau>; \<forall>s\<in>RED \<tau>. t[x::=s]\<in>RED \<sigma>\<rbrakk> \<Longrightarrow> App (Lam [x].t) u' \<in> RED \<sigma>"
      assume as1: "u \<in> RED \<tau>"
      assume as2: "\<forall>s\<in>RED \<tau>. t[x::=s]\<in>RED \<sigma>"
      have "CR3_RED (App (Lam [x].t) u) \<sigma>" unfolding CR3_RED_def
      proof(intro strip)
        fix r
        assume red: "App (Lam [x].t) u \<longrightarrow>\<^sub>\<beta> r"
        moreover
        { assume "\<exists>t'. t \<longrightarrow>\<^sub>\<beta> t' \<and> r = App (Lam [x].t') u"
          then obtain t' where a1: "t \<longrightarrow>\<^sub>\<beta> t'" and a2: "r = App (Lam [x].t') u" by blast
          have "App (Lam [x].t') u\<in>RED \<sigma>" using ih1 a1 as1 as2
            apply(auto)
            apply(drule_tac x="t'" in meta_spec)
            apply(simp)
            apply(drule meta_mp)
            prefer 2
            apply(auto)[1]
            apply(rule ballI)
            apply(drule_tac x="s" in bspec)
            apply(simp)
            apply(subgoal_tac "CR2 \<sigma>")(*A*)
            apply(unfold CR2_def)[1]
            apply(drule_tac x="t[x::=s]" in spec)
            apply(drule_tac x="t'[x::=s]" in spec)
            apply(simp add: beta_subst)
            (*A*)
            apply(simp add: RED_props)
            done
          then have "r\<in>RED \<sigma>" using a2 by simp
        }
        moreover
        { assume "\<exists>u'. u \<longrightarrow>\<^sub>\<beta> u' \<and> r = App (Lam [x].t) u'"
          then obtain u' where b1: "u \<longrightarrow>\<^sub>\<beta> u'" and b2: "r = App (Lam [x].t) u'" by blast
          have "App (Lam [x].t) u'\<in>RED \<sigma>" using ih2 b1 as1 as2
            apply(auto)
            apply(drule_tac x="u'" in meta_spec)
            apply(simp)
            apply(drule meta_mp)
            apply(subgoal_tac "CR2 \<tau>")
            apply(unfold CR2_def)[1]
            apply(drule_tac x="u" in spec)
            apply(drule_tac x="u'" in spec)
            apply(simp)
            apply(simp add: RED_props)
            apply(simp)
            done
          then have "r\<in>RED \<sigma>" using b2 by simp
        }
        moreover
        { assume "r = t[x::=u]"
          then have "r\<in>RED \<sigma>" using as1 as2 by auto
        }
        ultimately show "r \<in> RED \<sigma>" 
          (* one wants to use the strong elimination principle; for this one 
             has to know that x\<sharp>u *)
        apply(cases) 
        apply(auto simp add: lam.inject)
        apply(drule beta_abs)
        apply(auto)[1]
        apply(auto simp add: alpha subst_rename)
        done
    qed
    moreover 
    have "NEUT (App (Lam [x].t) u)" unfolding NEUT_def by (auto)
    ultimately show "App (Lam [x].t) u \<in> RED \<sigma>"  using RED_props by (simp add: CR3_def)
  qed
qed
qed

inductive reduction_len :: "lam \<Rightarrow> nat \<Rightarrow> bool" where
  "reduction_len t 0"
| "reduction_len t n \<Longrightarrow> t' \<longrightarrow>\<^sub>\<beta> t \<Longrightarrow> reduction_len t' (Suc n)"

(* definition "len_bound t n = (\<forall>i\<ge>n. \<not> reduction_len t i)" *)

inductive len_bound :: "lam \<Rightarrow> nat \<Rightarrow> bool" where
  len_bound_NORMAL[intro]: "NORMAL t \<Longrightarrow> len_bound t n"
| len_bound_succ[intro]: "(\<And>t'. t \<longrightarrow>\<^sub>\<beta> t' \<Longrightarrow> len_bound t' n) \<Longrightarrow> len_bound t (Suc n)"

lemma len_bound_0: assumes "len_bound t 0" shows "NORMAL t"
  using assms apply cases by simp

lemma mono_len_bound: 
  assumes "n \<le> m"
      and "len_bound t n"
  shows "len_bound t m"
proof -
  have "len_bound t (Suc n)" if n: "len_bound t n" for n
    using n apply (induction) by auto
  thus ?thesis using assms
    by (metis dec_induct)
qed

lemma beta_finite_branch: 
  "finite {t'. t \<longrightarrow>\<^sub>\<beta> t'}"
proof (nominal_induct t rule: lam.strong_induct)
case (Var n)
  have "{t'.  Var n \<longrightarrow>\<^sub>\<beta> t'} = {}"
    using NORMAL_Var NORMAL_def by auto
  thus ?case by auto
case (App t1 t2)
  have aux1: "\<And>a body. \<exists>a' body'. Lam [a].body = Lam [a'].body' \<and> a' \<sharp> t2"
  proof -
    fix a::name and body::lam
    obtain a'::name where "a' \<sharp> (t2,body)"  apply atomize_elim apply (rule exists_fresh') by (finite_guess)
    hence a't2: "a' \<sharp> t2" and a'body: "a' \<sharp> body" by auto
    define body' where "body' \<equiv> [(a, a')] \<bullet> body"
    have rename: "Lam [a].body = Lam [a'].body'"
      unfolding body'_def
      by (smt a'body alpha' lam.inject(3) perm_fresh_fresh perm_swap(1))
    show "?thesis a body"
      using a't2 rename by auto
  qed
  obtain a body where t1_lam: "t1 = Lam[a]. body \<or> \<not> (\<exists>a b. t1 = Lam[a]. b)" and "a \<sharp> t2"
    apply atomize_elim apply (nominal_induct t1 rule:"lam.strong_induct") apply (auto simp: exists_fresh' fs_name1)
    using aux1 by blast+
  let ?choices = "{App t1' t2 | t1'. t1 \<longrightarrow>\<^sub>\<beta> t1'} \<union> {App t1 t2' | t2'. t2 \<longrightarrow>\<^sub>\<beta> t2'}
                   \<union> {body[a::=t2]}"
  have "t' \<in> ?choices" if beta: "App t1 t2 \<longrightarrow>\<^sub>\<beta> t'" for t'
  using beta proof (cases)
    case (b1 s1 s2 t) thus ?thesis by (auto simp: lam.inject)
    next case b2 thus ?thesis by (auto simp: lam.inject)
    next case b3 thus ?thesis by (auto simp: lam.inject)
    next case (b4 a' s1 s2)
      hence t1:"t1 = Lam[a'].s2" and "t2 = s1" by (auto simp: lam.inject)
      with t1_lam have "t1 = Lam[a].body" by auto
      hence "Lam[a'].s2 = Lam[a].body"
        using t1 by auto
      hence "s2[a'::=s1] = body[a::=t2]"
        unfolding \<open>t2 = s1\<close>
        by (smt alpha lam.inject(3) subst_rename)
      with b4 show ?thesis by auto
    next case b5 thus ?thesis by (auto simp: lam.inject)
    next case b6 thus ?thesis by (auto simp: lam.inject)
    next case b7 thus ?thesis by (auto simp: lam.inject)
    next case b8 thus ?thesis by (auto simp: lam.inject)
    next case b9 thus ?thesis by (auto simp: lam.inject)
  qed

  hence "{t'.  App t1 t2 \<longrightarrow>\<^sub>\<beta> t'} \<subseteq> ?choices" by auto
  moreover have "finite ?choices" using App by auto
  ultimately show "finite {t'.  App t1 t2 \<longrightarrow>\<^sub>\<beta> t'}"
    using infinite_super by auto
next case (Lam a t)
  let ?choices = "{Lam [a].t' | t'. t \<longrightarrow>\<^sub>\<beta> t'}"
  have "{t'.  Lam [a].t \<longrightarrow>\<^sub>\<beta> t'} \<subseteq> ?choices"
    by (auto simp: beta_abs)
  moreover have "finite ?choices" using Lam by auto
  ultimately show ?case
    using infinite_super by auto
next case (MkPair t1 t2)
  let ?choices = "{MkPair t1' t2 | t1'. t1 \<longrightarrow>\<^sub>\<beta> t1'} \<union> {MkPair t1 t2' | t2'. t2 \<longrightarrow>\<^sub>\<beta> t2'}"
  have "{t'. MkPair t1 t2 \<longrightarrow>\<^sub>\<beta> t'} \<subseteq> ?choices"
    apply auto apply (cases rule: Beta.cases)
    by (auto simp: lam.inject)
  moreover have "finite ?choices" using MkPair by auto
  ultimately show ?case
    using infinite_super by auto
next case (Unpair b t)
  obtain t1 t2 where t_pair: "t = MkPair t1 t2 \<or> \<not> (\<exists>t1 t2. t = MkPair t1 t2)" by blast
  let ?choices = "{Unpair b t' | t'. t \<longrightarrow>\<^sub>\<beta> t'} \<union> {if b then t1 else t2}"
  have "t' \<in> ?choices" if beta: "Unpair b t \<longrightarrow>\<^sub>\<beta> t'" for t'
  using beta proof (cases)
    case (b1 s1 s2 t) thus ?thesis by (auto simp: lam.inject)
    next case b2 thus ?thesis by (auto simp: lam.inject)
    next case b3 thus ?thesis by (auto simp: lam.inject)
    next case b4 thus ?thesis by (auto simp: lam.inject)
    next case b5 thus ?thesis by (auto simp: lam.inject)
    next case b6 thus ?thesis by (auto simp: lam.inject)
    next case b7 thus ?thesis by (auto simp: lam.inject)
    next case (b8 s2)
      have b: "b = True" and t: "t = MkPair t' s2" using b8 by (auto simp: lam.inject)
      from t have "t'=t1" using t_pair by (auto simp: lam.inject)
      with b show ?thesis by auto
    next case (b9 s1)
      have b: "b = False" and t: "t = MkPair s1 t'" using b9 by (auto simp: lam.inject)
      from t have "t'=t2" using t_pair by (auto simp: lam.inject)
      with b show ?thesis by auto
  qed

  hence "{t'.  Unpair b t \<longrightarrow>\<^sub>\<beta> t'} \<subseteq> ?choices" by blast
  moreover have "finite ?choices" using Unpair by auto
  ultimately show "finite {t'.  Unpair b t \<longrightarrow>\<^sub>\<beta> t'}"
    using infinite_super by auto
qed

lemma SN_len_bound: 
  assumes "SN t"
  shows "\<exists>n. len_bound t n"
using assms proof (induction)
case (SN_intro t)
  define succ where "succ \<equiv> {t'. t \<longrightarrow>\<^sub>\<beta> t'}"
  have bounded: "\<And>t'. t' \<in> succ \<Longrightarrow> \<exists>n. len_bound t' n" using SN_intro.IH succ_def by auto
  have "finite succ" using succ_def beta_finite_branch by auto
  then obtain n where "\<And>t'. t' \<in> succ \<Longrightarrow> len_bound t' n"
  proof (atomize_elim, insert bounded, induction rule:finite_induct)
  case empty show ?case by simp
  next case (insert t F)
    obtain nx where nx: "len_bound t nx" using insert.prems by auto
    obtain nF where nF: "\<And>t'. t' \<in> F \<Longrightarrow> len_bound t' nF" using insert.prems insert.IH by auto
    show ?case 
      apply (rule exI[of _ "max nx nF"]) using nx nF
      apply (auto simp: max_def mono_len_bound)
      using mono_len_bound nat_le_linear by blast
  qed
  then have "len_bound t (Suc n)"
    apply (rule len_bound_succ) unfolding succ_def by simp
  thus ?case by auto
qed

lemma pair_RED:
  assumes s_RED: "s \<in> RED \<sigma>" and t_RED: "t \<in> RED \<tau>"
  shows "MkPair s t \<in> RED (TPair \<sigma> \<tau>)"
proof -
  from assms have "SN s" and "SN t"
    using CR1_def RED_props(1) by blast+
  from \<open>SN s\<close> obtain ns where ns: "len_bound s ns" apply atomize_elim by (rule SN_len_bound)
  from \<open>SN t\<close> obtain nt where nt: "len_bound t nt" apply atomize_elim by (rule SN_len_bound)
  define n where "n \<equiv> ns + nt"

  have fst_red: "Unpair True (MkPair s t) \<in> RED \<sigma>"
    using n_def[THEN meta_eq_to_obj_eq] ns nt s_RED
  proof (induction n arbitrary: ns nt s t rule:nat_less_induct)
  case (1 n)
    have "u \<in> RED \<sigma>" if beta: "Unpair True (MkPair s t) \<longrightarrow>\<^sub>\<beta> u" for u
    using beta proof cases
    case b1 thus ?thesis by auto
    next case b2 thus ?thesis by auto
    next case b3 thus ?thesis by auto
    next case b4 thus ?thesis by auto
    next case b5 thus ?thesis by auto
    next case b6 thus ?thesis by auto
    next case b9 thus ?thesis by (auto simp: lam.inject)
    next case (b8) thus ?thesis using 1 by (auto simp: lam.inject)
    next case (b7 s1 s' b)
      hence s': "MkPair s t \<longrightarrow>\<^sub>\<beta> s'" and u: "u = Unpair True s'" by (auto simp: lam.inject)
      show ?thesis
      using s' proof cases
      case b1 thus ?thesis by auto
      next case b2 thus ?thesis by auto
      next case b3 thus ?thesis by auto
      next case b4 thus ?thesis by auto
      next case b7 thus ?thesis by (auto simp: lam.inject)
      next case b8 thus ?thesis by (auto simp: lam.inject)
      next case b9 thus ?thesis by (auto simp: lam.inject)
      next case (b5 _ s'')
        hence s': "s' = MkPair s'' t" and ss'': "s \<longrightarrow>\<^sub>\<beta> s''" by (auto simp: lam.inject)
        obtain ns'' where ns'': "len_bound s'' ns''" and ns''_bound: "ns'' < ns"
          using `len_bound s ns` ss'' by (metis NORMAL_def len_bound.simps lessI)
        have s''_RED: "s'' \<in> RED \<sigma>" using ss'' "1.prems"
          using CR2_def RED_props(2) by blast
        have "Unpair True (MkPair s'' t) \<in> RED \<sigma>"
          apply (rule "1.IH"[rule_format, rotated 2]) 
             apply (fact ns'') apply (fact "1.prems") apply (fact s''_RED)
           by (simp_all add: "1.prems"(1) ns''_bound)
        thus ?thesis
          unfolding u s' by simp
      next case (b6 _ t'')
        hence s': "s' = MkPair s t''" and tt'': "t \<longrightarrow>\<^sub>\<beta> t''" by (auto simp: lam.inject)
        obtain nt'' where nt'': "len_bound t'' nt''" and nt''_bound: "nt'' < nt"
          using `len_bound t nt` tt'' by (metis NORMAL_def len_bound.simps lessI)
        have "Unpair True (MkPair s t'') \<in> RED \<sigma>"
          apply (rule "1.IH"[rule_format, rotated 2]) 
             apply (fact "1.prems") apply (fact nt'') apply (fact "1.prems")
           by (simp_all add: "1.prems"(1) nt''_bound)
        thus ?thesis
          unfolding u s' by simp
      qed
    qed
    thus ?case
      using CR3_RED_def CR3_def NEUT_def RED_props(3) by blast
  qed

  have snd_red: "Unpair False (MkPair s t) \<in> RED \<tau>"
    using n_def[THEN meta_eq_to_obj_eq] ns nt t_RED
  proof (induction n arbitrary: ns nt s t rule:nat_less_induct)
  case (1 n)
    have "u \<in> RED \<tau>" if beta: "Unpair False (MkPair s t) \<longrightarrow>\<^sub>\<beta> u" for u
    using beta proof cases
    case b1 thus ?thesis by auto
    next case b2 thus ?thesis by auto
    next case b3 thus ?thesis by auto
    next case b4 thus ?thesis by auto
    next case b5 thus ?thesis by auto
    next case b6 thus ?thesis by auto
    next case b8 thus ?thesis by (auto simp: lam.inject)
    next case b9 thus ?thesis using 1 by (auto simp: lam.inject)
    next case (b7 s1 s' b)
      hence s': "MkPair s t \<longrightarrow>\<^sub>\<beta> s'" and u: "u = Unpair False s'" by (auto simp: lam.inject)
      show ?thesis
      using s' proof cases
      case b1 thus ?thesis by auto
      next case b2 thus ?thesis by auto
      next case b3 thus ?thesis by auto
      next case b4 thus ?thesis by auto
      next case b7 thus ?thesis by (auto simp: lam.inject)
      next case b8 thus ?thesis by (auto simp: lam.inject)
      next case b9 thus ?thesis by (auto simp: lam.inject)
      next case (b5 _ s'')
        hence s': "s' = MkPair s'' t" and ss'': "s \<longrightarrow>\<^sub>\<beta> s''" by (auto simp: lam.inject)
        obtain ns'' where ns'': "len_bound s'' ns''" and ns''_bound: "ns'' < ns"
          using `len_bound s ns` ss'' by (metis NORMAL_def len_bound.simps lessI)
        have "Unpair False (MkPair s'' t) \<in> RED \<tau>"
          apply (rule "1.IH"[rule_format, rotated 2]) 
             apply (fact ns'') apply (fact "1.prems") apply (fact "1.prems")
           by (simp_all add: "1.prems"(1) ns''_bound)
        thus ?thesis
          unfolding u s' by simp
      next case (b6 _ t'')
        hence s': "s' = MkPair s t''" and tt'': "t \<longrightarrow>\<^sub>\<beta> t''" by (auto simp: lam.inject)
        obtain nt'' where nt'': "len_bound t'' nt''" and nt''_bound: "nt'' < nt"
          using `len_bound t nt` tt'' by (metis NORMAL_def len_bound.simps lessI)
        have t''_RED: "t'' \<in> RED \<tau>" using tt'' "1.prems"
          using CR2_def RED_props(2) by blast
        have "Unpair False (MkPair s t'') \<in> RED \<tau>"
          apply (rule "1.IH"[rule_format, rotated 2]) 
             apply (fact "1.prems") apply (fact nt'') apply (fact t''_RED)
           by (simp_all add: "1.prems"(1) nt''_bound)
        thus ?thesis
          unfolding u s' by simp
      qed
    qed
    thus ?case
      using CR3_RED_def CR3_def NEUT_def RED_props(3) by blast
  qed


  show "MkPair s t \<in> RED (TPair \<sigma> \<tau>)"
    using fst_red snd_red by simp 
qed

abbreviation 
 mapsto :: "(name\<times>lam) list \<Rightarrow> name \<Rightarrow> lam \<Rightarrow> bool" ("_ maps _ to _" [55,55,55] 55) 
where
 "\<theta> maps x to e \<equiv> (lookup \<theta> x) = e"

abbreviation 
  closes :: "(name\<times>lam) list \<Rightarrow> (name\<times>ty) list \<Rightarrow> bool" ("_ closes _" [55,55] 55) 
where
  "\<theta> closes \<Gamma> \<equiv> \<forall>x T. ((x,T) \<in> set \<Gamma> \<longrightarrow> (\<exists>t. \<theta> maps x to t \<and> t \<in> RED T))"

lemma all_RED: 
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  and     b: "\<theta> closes \<Gamma>"
  shows "\<theta><t> \<in> RED \<tau>"
using a b
proof(nominal_induct  avoiding: \<theta> rule: typing.strong_induct)
  case (t3 a \<Gamma> \<sigma> t \<tau> \<theta>) --"lambda case"
  have ih: "\<And>\<theta>. \<theta> closes ((a,\<sigma>)#\<Gamma>) \<Longrightarrow> \<theta><t> \<in> RED \<tau>" by fact
  have \<theta>_cond: "\<theta> closes \<Gamma>" by fact
  have fresh: "a\<sharp>\<Gamma>" "a\<sharp>\<theta>" by fact+
  from ih have "\<forall>s\<in>RED \<sigma>. ((a,s)#\<theta>)<t> \<in> RED \<tau>" using fresh \<theta>_cond fresh_context by simp
  then have "\<forall>s\<in>RED \<sigma>. \<theta><t>[a::=s] \<in> RED \<tau>" using fresh by (simp add: psubst_subst)
  then have "Lam [a].(\<theta><t>) \<in> RED (\<sigma> \<rightarrow> \<tau>)" by (simp only: abs_RED)
  then show "\<theta><(Lam [a].t)> \<in> RED (\<sigma> \<rightarrow> \<tau>)" using fresh by simp
next
  case (t4 \<Gamma> t1 \<tau> t2 \<sigma>) thus ?case
    using pair_RED psubst.simps(3) by presburger
qed auto

section {* identity substitution generated from a context \<Gamma> *}
fun
  "id" :: "(name\<times>ty) list \<Rightarrow> (name\<times>lam) list"
where
  "id []    = []"
| "id ((x,\<tau>)#\<Gamma>) = (x,Var x)#(id \<Gamma>)"

lemma id_maps:
  shows "(id \<Gamma>) maps a to (Var a)"
by (induct \<Gamma>) (auto)

lemma id_fresh:
  fixes a::"name"
  assumes a: "a\<sharp>\<Gamma>"
  shows "a\<sharp>(id \<Gamma>)"
using a
by (induct \<Gamma>)
   (auto simp add: fresh_list_nil fresh_list_cons)

lemma id_apply:  
  shows "(id \<Gamma>)<t> = t"
by (nominal_induct t avoiding: \<Gamma> rule: lam.strong_induct)
   (auto simp add: id_maps id_fresh)

lemma id_closes:
  shows "(id \<Gamma>) closes \<Gamma>"
apply(auto)
apply(simp add: id_maps)
apply(subgoal_tac "CR3 T") --"A"
apply(drule CR3_implies_CR4)
apply(simp add: CR4_def)
apply(drule_tac x="Var x" in spec)
apply(force simp add: NEUT_def NORMAL_Var)
--"A"
apply(rule RED_props)
done

lemma typing_implies_RED:  
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  shows "t \<in> RED \<tau>"
proof -
  have "(id \<Gamma>)<t>\<in>RED \<tau>" 
  proof -
    have "(id \<Gamma>) closes \<Gamma>" by (rule id_closes)
    with a show ?thesis by (rule all_RED)
  qed
  thus"t \<in> RED \<tau>" by (simp add: id_apply)
qed

lemma typing_implies_SN: 
  assumes a: "\<Gamma> \<turnstile> t : \<tau>"
  shows "SN(t)"
proof -
  from a have "t \<in> RED \<tau>" by (rule typing_implies_RED)
  moreover
  have "CR1 \<tau>" by (rule RED_props)
  ultimately show "SN(t)" by (simp add: CR1_def)
qed

end