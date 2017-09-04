theory Hoare_Untyped
imports Lang_Untyped "HOL-Library.Rewrite"
begin

definition hoare_untyped :: "(memory \<Rightarrow> bool) \<Rightarrow> program_rep \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "hoare_untyped pre prog post =
  (\<forall>m. pre m \<longrightarrow> (\<forall>m'. m' \<in> support_distr (denotation_untyped prog m) 
                  \<longrightarrow> post m'))"
                                                                               
definition hoare_denotation :: "(memory \<Rightarrow> bool) \<Rightarrow> _ \<Rightarrow> (memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "hoare_denotation pre prog post = (\<forall>m. pre m \<longrightarrow> (\<forall>m'. m' \<in> support_distr (prog m) \<longrightarrow> post m'))"
lemma hoare_denotation_0': 
  assumes "\<And>m. P m \<Longrightarrow> f m = 0"
  shows "hoare_denotation P f Q"
unfolding hoare_denotation_def using assms by auto

lemma hoare_denotation_0 [simp]: "hoare_denotation P (\<lambda>m. 0) Q"
  apply (rule hoare_denotation_0') by simp

lemma hoare_untyped_hoare_denotation: "hoare_untyped pre c post = hoare_denotation pre (denotation_untyped c) post"
  unfolding hoare_untyped_def hoare_denotation_def ..

lemma readonly_hoare_untyped:
  shows "program_untyped_readonly X c = (\<forall>a. hoare_untyped (\<lambda>m. \<forall>x\<in>X. memory_lookup_untyped m x = a x) c (\<lambda>m. \<forall>x\<in>X. memory_lookup_untyped m x = a x))"
unfolding program_untyped_readonly_def hoare_untyped_hoare_denotation hoare_denotation_def denotation_readonly_def 
by metis

(* lemma readonly_notin_vars: (* TODO: rephrase using readonly_program_untyped or something, or drop *)
(* See program_untyped_readonly_write_vars below *)
  fixes x::variable_untyped and a::val and c::program_rep
  assumes "x\<notin>set(vars_untyped c)"
  shows "hoare_untyped (\<lambda>m. memory_lookup_untyped m x = a) c (\<lambda>m. memory_lookup_untyped m x = a)"
 *)

(* lemma readonly_assign: (* TODO: rephrase using readonly_program_untyped or something, or drop *)
(* See program_untyped_readonly_write_vars below *)
  fixes x::pattern_untyped and y::variable_untyped and e::expression_untyped and a::val
  assumes "y\<notin>set(p_vars x)"
  shows "hoare_untyped (\<lambda>m. memory_lookup_untyped m y = a) (Assign x e) (\<lambda>m. memory_lookup_untyped m y = a)"
 *)

definition "assertion_footprint X P == (\<forall>m1 m2. (\<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x) \<longrightarrow> P m1 = P m2)"
lemma assertion_footprint_const: "assertion_footprint X (\<lambda>m. P)"
  unfolding assertion_footprint_def by simp
lemma assertion_footprint_app: "assertion_footprint X P \<Longrightarrow> assertion_footprint X Q \<Longrightarrow> assertion_footprint X (\<lambda>m. (P m) (Q m))"
  unfolding assertion_footprint_def by metis 


lemma conseq_rule:
  assumes "\<forall>m. P m \<longrightarrow> P' m"
      and "\<forall>m. Q' m \<longrightarrow> Q m"
      and "hoare_untyped P' c Q'"
  shows "hoare_untyped P c Q"
  using assms unfolding hoare_untyped_def by auto

lemma seq_rule:
  fixes P Q R c d
  assumes "hoare_untyped P c Q" and "hoare_untyped Q d R"
  shows "hoare_untyped P (Seq c d) R"
  using assms unfolding hoare_untyped_def by auto

lemma assign_rule:
  fixes P Q xs gs e
  assumes "\<forall>m. P m \<longrightarrow> Q (memory_update_untyped_pattern m pat (eu_fun e m))"
  shows "hoare_untyped P (Assign pat e) Q"
  using assms unfolding hoare_untyped_def by simp

lemma sample_rule: 
  fixes P Q xs gs e
  assumes "\<forall>m. P m \<longrightarrow> (\<forall>v\<in>support_distr (ed_fun e m). Q (memory_update_untyped_pattern m pat v))"
  shows "hoare_untyped P (Sample pat e) Q"
  using assms unfolding hoare_untyped_def by auto

lemma hoare_denotation_sup:
  assumes "incseq c"
  assumes hoare: "\<And>n::nat. hoare_denotation P (c n) Q"
  shows "hoare_denotation P (\<lambda>m. SUP n. c n m) Q"
proof (unfold hoare_denotation_def, auto)
  fix m m' assume "P m"
  assume m': "m' \<in> support_distr (SUP n. c n m)"
  {assume "\<And>n. m' \<notin> support_distr (c n m)"
  hence "\<And>n. ennreal_Rep_distr (c n m) m' \<le> 0" 
    unfolding support_distr_def' using le_less_linear by blast
  hence "ennreal_Rep_distr (SUP n. c n m) m' \<le> 0"
    apply (subst ennreal_Rep_SUP_distr)
     close (metis (mono_tags, lifting) assms(1) incseq_def le_funD)
    by (simp add: SUP_le_iff) 
  hence "m' \<notin> support_distr (SUP n. c n m)"
    unfolding support_distr_def' by auto}
  with m' obtain n where "m' \<in> support_distr (c n m)" 
    by auto
  with hoare and `P m` show "Q m'"
    unfolding hoare_denotation_def by auto
qed

lemma while_rule:
  fixes P Q I c p
  assumes hoare: "hoare_untyped (\<lambda>m. I m \<and> eu_fun e m = embedding True) p I"
      and PI: "\<forall>m. P m \<longrightarrow> I m"
      and IQ: "\<forall>m. eu_fun e m \<noteq> embedding True \<longrightarrow> I m \<longrightarrow> Q m"
  shows "hoare_untyped P (While e p) Q"
proof -
  have inc: "incseq (\<lambda>n. while_denotation_n n (\<lambda>m. eu_fun e m = embedding True) (denotation_untyped p))"
    using mono_while_denotation_n unfolding mono_def le_fun_def by simp
  {fix n
  have "hoare_denotation I (while_denotation_n n (\<lambda>m. eu_fun e m = embedding True) (denotation_untyped p)) Q"
  proof (induct n)
  case 0 show ?case by simp
  next case (Suc n)
    show ?case
    proof (unfold hoare_denotation_def, auto)
      fix m m' x
      assume true: "eu_fun e m = embedding True"
        and Im: "I m" and x: "x \<in> support_distr (denotation_untyped p m)"
        and m': "m' \<in> support_distr (while_denotation_n n (\<lambda>m. eu_fun e m = embedding True) (denotation_untyped p) x)"
      (* from P and PI have I: "I m" by simp *)
      from true hoare x Im have Ix: "I x"
        unfolding hoare_untyped_def by auto
      from Ix m' Suc show "Q m'" 
        unfolding hoare_denotation_def by auto
    next
      fix m assume not_true: "eu_fun e m \<noteq> embedding True" and I: "I m"
      (* from P have I: "I m" using PI by auto *)
      from not_true and I and IQ 
      show "Q m" by auto
    qed
  qed
  }
  hence n: "\<And>n. hoare_denotation P (while_denotation_n n (\<lambda>m. eu_fun e m = embedding True) (denotation_untyped p)) Q"
    unfolding hoare_denotation_def using PI by auto
  show ?thesis
    unfolding hoare_untyped_hoare_denotation
    unfolding denotation_untyped_While[THEN ext]
    apply (rule hoare_denotation_sup)
     close (fact inc)
    by (fact n)
qed

lemma iftrue_rule:
  fixes P Q I c p1 p2
  assumes "hoare_untyped P p1 Q"
          "\<forall>m. P m \<longrightarrow> eu_fun e m = embedding True"
  shows "hoare_untyped P (IfTE e p1 p2) Q"
  using assms unfolding hoare_untyped_def by auto

lemma iffalse_rule:
  fixes P Q I c p1 p2
  assumes "hoare_untyped P p2 Q"
          "\<forall>m. P m \<longrightarrow> eu_fun e m \<noteq> embedding True"
  shows "hoare_untyped P (IfTE e p1 p2) Q"
  using assms unfolding hoare_untyped_def by simp

lemma true_rule: "(\<forall>m. Q m) \<Longrightarrow> hoare_untyped P c Q"
  unfolding hoare_untyped_def by simp

lemma skip_rule:
  assumes "\<forall>m. P m \<longrightarrow> Q m"
  shows "hoare_untyped P Skip Q"
  unfolding hoare_untyped_def using assms by simp

lemma case_rule:
  assumes "\<And>x. hoare_untyped (\<lambda>m. P m \<and> f m = x) c Q"
  shows "hoare_untyped P c Q"
using assms unfolding hoare_untyped_def by metis

lemma if_case_rule:
  assumes "hoare_untyped P1 c1 Q"
  assumes "hoare_untyped P2 c2 Q"
  shows "hoare_untyped (\<lambda>m. if eu_fun e m = embedding True then P1 m else P2 m) (IfTE e c1 c2) Q"
  apply (rule case_rule[where f="\<lambda>m. (eu_fun e m = embedding True)"])
  apply (case_tac x, auto)
  apply (rule iftrue_rule)
  apply (rule conseq_rule[where P'=P1 and Q'=Q], auto simp: assms)
  apply (rule iffalse_rule)
  by (rule conseq_rule[where P'=P2 and Q'=Q], auto simp: assms)

lemma program_untyped_readonly_write_vars: "program_untyped_readonly (- set(write_vars_untyped p)) p"
proof -
  have assign_aux: "\<And>x e m a y. y\<notin>set(pu_vars x) \<Longrightarrow> memory_lookup_untyped m y = a y \<Longrightarrow>
             memory_lookup_untyped (memory_update_untyped_pattern m x (eu_fun e m)) y = a y"
    proof -
      fix x e m a y assume y: "y\<notin>set (pu_vars x)"
      assume "memory_lookup_untyped m y = a y"
      thus "memory_lookup_untyped (memory_update_untyped_pattern m x (eu_fun e m)) y = a y"
        by (simp add: y memory_lookup_update_pattern_notsame)
    qed

  fix q
  have "\<And>R. set (write_vars_untyped p) \<inter> R = {} \<Longrightarrow> program_untyped_readonly R p"
    and "\<And>R. set (write_vars_proc_untyped q) \<inter> R = {} \<Longrightarrow> 
          program_untyped_readonly (R\<inter>Collect vu_global) (case q of Proc body a r \<Rightarrow> body | _ \<Rightarrow> Skip)" 
  proof (induct p and q)
  case (Assign x e)
    show ?case  
      apply (subst readonly_hoare_untyped, rule allI)
      apply (rule Hoare_Untyped.assign_rule)
      using assign_aux Assign.prems by fastforce
  next
  case (Sample x e)
    show ?case  
      apply (subst readonly_hoare_untyped, rule allI)
      apply (rule Hoare_Untyped.sample_rule)
      using assign_aux Sample.prems memory_lookup_update_pattern_notsame by fastforce
  next
  case (Seq p1 p2)
    have p1: "\<And>a. hoare_untyped (\<lambda>m. \<forall>x\<in>R. memory_lookup_untyped m x = a x) p1 (\<lambda>m. \<forall>x\<in>R. memory_lookup_untyped m x = a x)"
     and p2: "\<And>a. hoare_untyped (\<lambda>m. \<forall>x\<in>R. memory_lookup_untyped m x = a x) p2 (\<lambda>m. \<forall>x\<in>R. memory_lookup_untyped m x = a x)"
      using Seq.hyps[where R=R] unfolding readonly_hoare_untyped using Seq.prems by auto
    show ?case
      apply (subst readonly_hoare_untyped, rule allI)
      apply (rule Hoare_Untyped.seq_rule)
      close (fact p1) by (fact p2)
  next
  case Skip show ?case
    using denotation_readonly_def program_untyped_readonly_def by auto 
  next
  case (IfTE e p1 p2)
    have p1: "\<And>a. hoare_untyped (\<lambda>m. \<forall>x\<in>R. memory_lookup_untyped m x = a x) p1 (\<lambda>m. \<forall>x\<in>R. memory_lookup_untyped m x = a x)"
     and p2: "\<And>a. hoare_untyped (\<lambda>m. \<forall>x\<in>R. memory_lookup_untyped m x = a x) p2 (\<lambda>m. \<forall>x\<in>R. memory_lookup_untyped m x = a x)"
      using IfTE.hyps[where R=R] unfolding readonly_hoare_untyped using IfTE.prems by auto
    have t: "\<And>a. hoare_untyped (\<lambda>m. if eu_fun e m = embedding True then \<forall>x\<in>R. memory_lookup_untyped m x = a x else \<forall>x\<in>R. memory_lookup_untyped m x = a x)
        (IfTE e p1 p2) (\<lambda>m::memory. \<forall>x::variable_untyped\<in>R. memory_lookup_untyped m x = a x)"
      apply (rule Hoare_Untyped.if_case_rule) using p1 close simp using p2 by simp
    show ?case
      apply (subst readonly_hoare_untyped, rule allI)
      using t by simp
  next
  case (While e p)
    have p: "\<And>a. hoare_untyped (\<lambda>m. \<forall>x\<in>R. memory_lookup_untyped m x = a x) p (\<lambda>m. \<forall>x\<in>R. memory_lookup_untyped m x = a x)"
      using While.hyps[where R=R] unfolding readonly_hoare_untyped using While.prems by auto
    have p': "\<And>a. hoare_untyped (\<lambda>m. (\<forall>x\<in>R. memory_lookup_untyped m x = a x) \<and> eu_fun e m = embedding True)
        p (\<lambda>m::memory. \<forall>x::variable_untyped\<in>R. memory_lookup_untyped m x = a x)"
      apply (rule Hoare_Untyped.conseq_rule) defer defer close (fact p) by auto
    show ?case
      apply (subst readonly_hoare_untyped, rule allI)
      apply (rule Hoare_Untyped.while_rule[where I="\<lambda>m. \<forall>x\<in>R. memory_lookup_untyped m x = _ x"])
      using p' by auto
  next 
  case (CallProc x p a)
    show ?case
    proof (cases p)
    case (Proc body pargs ret)  
      show ?thesis
        unfolding program_untyped_readonly_def denotation_readonly_def
      proof (rule+)
        fix m m' y
        define den where "den == denotation_untyped (CallProc x (Proc body pargs ret) a) m"
        assume m': "m' \<in> support_distr (denotation_untyped (CallProc x p a) m)"
        (* hence m': "Rep_distr den m' \<noteq> 0" by (simp add: den_def Proc support_distr_def) *)
        assume "y \<in> R"
        hence y_nin: "y \<notin> set (pu_vars x)" 
          using CallProc.prems by auto
        (* have cases: "\<And>P. \<lbrakk> \<not> vu_global y \<Longrightarrow> P; True \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" by auto *)
        obtain r a' b where den2: "den == apply_to_distr (\<lambda>m'::memory. memory_update_untyped_pattern (restore_locals m m') x (r m')) b"
                    and b: "b = denotation_untyped body (memory_update_untyped_pattern (init_locals m) pargs a')"
          unfolding den_def by auto
        then obtain m'' where m''1: "m'' \<in> support_distr b" and m''2: "m' = memory_update_untyped_pattern (restore_locals m m'') x (r m'')"
          using Proc den_def m' by auto
        show "Rep_memory m y = Rep_memory m' y"                               
        proof (cases "vu_global y")
          assume local: "\<not> vu_global y"
          with y_nin have "Rep_memory m' y = Rep_memory (restore_locals m m'') y"
            by (metis m''2 memory_lookup_update_pattern_notsame)
          thus "Rep_memory m y = Rep_memory m' y"
            by (simp add: Rep_restore_locals local)
        next
          assume global: "vu_global y" 
          define m_init where "m_init == init_locals m"
          define m_args where "m_args == memory_update_untyped_pattern m_init pargs a'"
          have y_nin2: "y \<notin> set (pu_vars pargs)"
            using `y \<in> R` CallProc.prems global unfolding Proc by auto
          have "Rep_memory m y = Rep_memory m_init y"
            by (simp add: Rep_init_locals global m_init_def)
          also have "\<dots> = Rep_memory m_args y"
            using m_args_def memory_lookup_update_pattern_notsame y_nin2 by auto
          also have b: "b = denotation_untyped body m_args"
            using b m_args_def m_init_def by auto
          have yR: "y \<in> (R\<inter>Collect vu_global)" using global `y\<in>R` by auto
          have "(set (pu_vars pargs) \<inter> Collect vu_global \<union> set (write_vars_untyped body) \<inter> Collect vu_global) \<inter> R = {}"
            using CallProc.prems unfolding Proc by auto
          hence "program_untyped_readonly (R\<inter>Collect vu_global) body"
            using CallProc.hyps unfolding Proc by simp
          with b m''1 yR have "Rep_memory m'' y = Rep_memory m_args y"
            by (metis denotation_readonly_def program_untyped_readonly_def)
          also have "Rep_memory m'' y = Rep_memory m' y"
            using Rep_restore_locals global m''2 memory_lookup_update_pattern_notsame y_nin by auto
          finally show "Rep_memory m y = Rep_memory m' y" by simp
        qed
      qed
    qed (auto simp: program_untyped_readonly_def denotation_untyped_CallProc_bad[THEN ext])
  next
  case (Proc body a r) 
    have "set (write_vars_untyped body) \<inter> (Collect vu_global \<inter> R) = {}"
      using Proc.prems by auto
    hence "program_untyped_readonly (Collect vu_global \<inter> R) body"
      using Proc.hyps by simp
    thus ?case by (simp add: Int_commute)
  next
  case ProcRef show ?case 
    unfolding program_untyped_readonly_def denotation_readonly_def by simp
  next
  case ProcAbs show ?case
    unfolding program_untyped_readonly_def denotation_readonly_def by simp
  next
  case ProcAppl show ?case
    unfolding program_untyped_readonly_def denotation_readonly_def by simp
  next
  case ProcPair show ?case
    unfolding program_untyped_readonly_def denotation_readonly_def by simp
  next
  case ProcUnpair show ?case
    unfolding program_untyped_readonly_def denotation_readonly_def by simp
  next case ProcUnit show ?case
    unfolding program_untyped_readonly_def denotation_readonly_def by simp
  qed
  thus ?thesis by simp
qed


lemma seq_swap_untyped:
  fixes A B R
  assumes a_ro: "program_untyped_readonly R a"
  assumes b_ro: "program_untyped_readonly R b"
  assumes foot_a: "program_untyped_footprint A a"
  assumes foot_b: "program_untyped_footprint B b"
  assumes ABR: "A\<inter>B\<subseteq>R"
  shows "denotation_untyped (Seq a b) m = denotation_untyped (Seq b a) m"
apply (subst ennreal_Rep_distr_inject[symmetric], rule ext, rename_tac m2)
proof (case_tac "\<forall>x\<in>R. Rep_memory m x = Rep_memory m2 x")
  fix m2 assume same_R: "\<forall>x\<in>R. Rep_memory m x = Rep_memory m2 x"
  define aa bb 
    where "aa == (\<lambda>m. ennreal_Rep_distr (denotation_untyped a m))"
      and "bb == (\<lambda>m. ennreal_Rep_distr (denotation_untyped b m))"

  have aa_pos [simp]: "\<And>x y. aa x y \<ge> 0"
    by (simp add: aa_def) 
  have bb_pos [simp]: "\<And>x y. bb x y \<ge> 0"
    by (simp add: bb_def) 

  define A' B' where "A' == A-R" and "B' == -A-R"
  have A'RB': "(A'\<union>R) = -B'" unfolding A'_def B'_def by auto

  have ro_B'_a: "program_untyped_readonly B' a"
    apply (rule program_untyped_footprint_readonly)
    defer close (fact foot_a)
    unfolding B'_def by auto
  hence ro_B'R_a: "program_untyped_readonly (B'\<union>R) a"
    using a_ro unfolding program_untyped_readonly_def
    by (rule denotation_readonly_union)
    
  have ro_A'_b: "program_untyped_readonly A' b"
    apply (rule program_untyped_footprint_readonly)
    defer close (fact foot_b)
    unfolding A'_def using ABR by auto

  have ro_A'R_b: "program_untyped_readonly (A'\<union>R) b"
    apply (rewrite at "A'\<union>R" to "(A-R)\<union>R" eq_reflection)
     close (simp add: A'_def)
    apply (rule program_untyped_readonly_union)
    apply (rule program_untyped_footprint_readonly)
      defer close (fact foot_b) close (fact b_ro)
    using ABR by auto

  have foot_A'R_a: "program_untyped_footprint (A'\<union>R) a"
    apply (rule program_untyped_footprint_mono) defer apply (fact foot_a)
    unfolding A'_def by simp

  have foot_B'R_b: "program_untyped_footprint (B'\<union>R) b"
    apply (rule program_untyped_footprint_mono) defer apply (fact foot_b)
    unfolding B'_def using ABR by auto

  have seq_a_b: "ennreal_Rep_distr (denotation_untyped (Seq a b) m) m2 = aa m (memory_combine A' m2 m) * bb (memory_combine A' m2 m) m2"
  proof -
    have seq_distr: "ennreal_Rep_distr (denotation_untyped (Seq a b) m) m2 = (\<integral>\<^sup>+m1. aa m m1 * bb m1 m2 \<partial>count_space UNIV)" 
      by (simp add: ennreal_Rep_compose_distr aa_def bb_def) 
    let ?mix = "memory_combine A' m2 m"
    {fix m1 consider "m1=?mix" | "aa m m1 * bb m1 m2 = 0" | "m1\<noteq>?mix" and "aa m m1 * bb m1 m2 \<noteq> 0" by auto}
    then have m2_single: "\<And>m1. aa m m1 * bb m1 m2 = aa m m1 * bb m1 m2 * indicator {?mix} m1"
    proof cases
      fix m1 assume "m1=?mix" thus "?thesis m1" by simp
    next
      fix m1 assume "aa m m1 * bb m1 m2 = 0"
      thus "?thesis m1" by auto
    next
      fix m1 assume "m1\<noteq>?mix" 
      assume "aa m m1 * bb m1 m2 \<noteq> 0"
      with aa_pos bb_pos have aa: "aa m m1 > 0" and bb: "bb m1 m2 > 0" 
        using gr_zeroI by auto
      have mm1B'R: "\<forall>x\<in>B'\<union>R. Rep_memory m x = Rep_memory m1 x"
        using aa `program_untyped_readonly (B'\<union>R) a` unfolding aa_def program_untyped_readonly_def denotation_readonly_def support_distr_def' by auto
      have m1m2A': "\<forall>x\<in>A'. Rep_memory m1 x = Rep_memory m2 x"
        using bb `program_untyped_readonly A' b` unfolding bb_def program_untyped_readonly_def denotation_readonly_def support_distr_def' by auto
      have "m1 = ?mix"
        apply (rule Rep_memory_inject[THEN iffD1], rule ext, auto)
         using m1m2A' apply blast
        by (metis A'_def B'_def ComplI Compl_Diff_eq Un_Diff_cancel2 mm1B'R)
      with `m1\<noteq>?mix` show "?thesis m1" by simp
    qed
    show "ennreal_Rep_distr (denotation_untyped (Seq a b) m) m2 = aa m ?mix * bb ?mix m2" 
      unfolding seq_distr apply (subst m2_single)
      apply (subst nn_integral_singleton_indicator_countspace)
      using aa_pos bb_pos by auto
  qed

  have seq_b_a: "ennreal_Rep_distr (denotation_untyped (Seq b a) m) m2 = bb m (memory_combine B' m2 m) * aa (memory_combine B' m2 m) m2" 
  proof -
    have seq_distr: "ennreal_Rep_distr (denotation_untyped (Seq b a) m) m2 = (\<integral>\<^sup>+m1. bb m m1 * aa m1 m2 \<partial>count_space UNIV)" 
      by (simp add: ennreal_Rep_compose_distr aa_def bb_def) 
    let ?mix = "memory_combine B' m2 m"
    have aux_cases: "\<And>P m1. \<lbrakk> m1=?mix \<Longrightarrow> P; bb m m1 * aa m1 m2 = 0 \<Longrightarrow> P;
                              m1\<noteq>?mix \<Longrightarrow>  bb m m1 * aa m1 m2 \<noteq> 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" by auto
    have m2_single: "\<And>m1. bb m m1 * aa m1 m2 = bb m m1 * aa m1 m2 * indicator {?mix} m1"
    proof (rule aux_cases)
      fix m1 assume "m1=?mix" thus "?thesis m1" by simp
    next
      fix m1 assume "bb m m1 * aa m1 m2 = 0"
      thus "?thesis m1" by auto
    next
      fix m1 assume "m1\<noteq>?mix" 
      assume "bb m m1 * aa m1 m2 \<noteq> 0"
      with aa_pos bb_pos have bb: "bb m m1 > 0" and aa: "aa m1 m2 > 0" 
        using gr_zeroI by auto
      have mm1A'R: "\<forall>x\<in>A'\<union>R. Rep_memory m x = Rep_memory m1 x"
        using bb `program_untyped_readonly (A'\<union>R) b` unfolding bb_def program_untyped_readonly_def denotation_readonly_def support_distr_def' by auto
      have m1m2B': "\<forall>x\<in>B'. Rep_memory m1 x = Rep_memory m2 x"
        using aa `program_untyped_readonly B' a` unfolding aa_def program_untyped_readonly_def denotation_readonly_def support_distr_def' by auto
      have "m1 = ?mix"
        apply (rule Rep_memory_inject[THEN iffD1], rule ext, auto)
         using m1m2B' apply blast
          using A'RB' mm1A'R by force
      with `m1\<noteq>?mix` show "?thesis m1" by simp
    qed
    show "ennreal_Rep_distr (denotation_untyped (Seq b a) m) m2 = bb m ?mix * aa ?mix m2" 
      unfolding seq_distr apply (subst m2_single)
      apply (subst nn_integral_singleton_indicator_countspace)
      using aa_pos bb_pos by auto
  qed
    
  note foot_A'R_a_rule = foot_A'R_a[unfolded program_untyped_footprint_def denotation_footprint_def', rule_format]
  have A'RA'_A'R: "memory_combine (A' \<union> R) default (memory_combine A' m2 m) = memory_combine (A' \<union> R) default m"
    apply (subst Rep_memory_inject[symmetric]) by auto
  have A'R_m2: "memory_combine (A' \<union> R) (memory_combine A' m2 m) m2 = m2"
    apply (subst Rep_memory_inject[symmetric], rule ext) unfolding Rep_memory_combine 
    using same_R by auto
  have A'R_B': "memory_combine (A' \<union> R) m m2 = memory_combine B' m2 m"
    apply (subst Rep_memory_inject[symmetric], rule ext) unfolding Rep_memory_combine by (simp add: A'RB') 

  have aa_rw: "aa m (memory_combine A' m2 m) = aa (memory_combine B' m2 m) m2"
    unfolding aa_def apply (subst foot_A'R_a_rule[where z=m2]) unfolding A'RA'_A'R A'R_m2 A'R_B' by auto

  note foot_B'R_b_rule = foot_B'R_b[unfolded program_untyped_footprint_def denotation_footprint_def', rule_format]
  have B'RA'_m: "memory_combine (B' \<union> R) (memory_combine A' m2 m) m = m"
    apply (subst Rep_memory_inject[symmetric], rule ext) unfolding Rep_memory_combine using A'RB' same_R by auto
  have B'R_B': "memory_combine (B' \<union> R) m2 m = memory_combine B' m2 m"
    apply (subst Rep_memory_inject[symmetric], rule ext) unfolding Rep_memory_combine using same_R by auto
  have B'R_default: "memory_combine (B' \<union> R) default (memory_combine A' m2 m) = memory_combine (B' \<union> R) default m2"
    apply (subst Rep_memory_inject[symmetric], rule ext) unfolding Rep_memory_combine using A'RB' by auto
  have bb_rw: "bb (memory_combine A' m2 m) m2 = bb m (memory_combine B' m2 m)"
    unfolding bb_def apply (subst foot_B'R_b_rule[where z=m]) unfolding B'RA'_m B'R_B' B'R_default by auto

  show "ennreal_Rep_distr (denotation_untyped (Seq a b) m) m2 = ennreal_Rep_distr (denotation_untyped (Seq b a) m) m2"
    unfolding seq_a_b seq_b_a aa_rw bb_rw by (simp add: mult.commute) 
next
  fix m2 assume notsame_R: "\<not> (\<forall>x\<in>R. Rep_memory m x = Rep_memory m2 x)"
  define aa bb eq
    where "aa == (\<lambda>m. ennreal_Rep_distr (denotation_untyped a m))"
      and "bb == (\<lambda>m. ennreal_Rep_distr (denotation_untyped b m))"
      and "eq == \<lambda>m'. \<forall>x\<in>R. memory_lookup_untyped m' x = memory_lookup_untyped m x"
  have not_eq: "\<not> eq m2" using notsame_R unfolding eq_def by metis
  have hoarea: "hoare_untyped eq a eq"
    using a_ro[unfolded readonly_hoare_untyped, rule_format, of "Rep_memory m"] unfolding eq_def by auto
  have hoareb: "hoare_untyped eq b eq"
    using b_ro[unfolded readonly_hoare_untyped, rule_format, of "Rep_memory m"] unfolding eq_def by auto

  have hoareab: "hoare_untyped eq (Seq a b) eq"
    using hoarea hoareb by (rule Hoare_Untyped.seq_rule)
  have "eq m" unfolding eq_def by simp
  with hoareab have "m2 \<in> support_distr (denotation_untyped (Seq a b) m) \<Longrightarrow> eq m2"
    unfolding hoare_untyped_hoare_denotation hoare_denotation_def by simp
  with not_eq have "m2 \<notin> support_distr (denotation_untyped (Seq a b) m)" by auto
  hence ab_0: "ennreal_Rep_distr (denotation_untyped (Seq a b) m) m2 = 0"
    unfolding support_distr_def'' by auto

  have hoareba: "hoare_untyped eq (Seq b a) eq"
    using hoareb hoarea by (rule Hoare_Untyped.seq_rule)
  have "eq m" unfolding eq_def by simp
  with hoareba have "m2 \<in> support_distr (denotation_untyped (Seq b a) m) \<Longrightarrow> eq m2"
    unfolding hoare_untyped_hoare_denotation hoare_denotation_def by simp
  with not_eq have "m2 \<notin> support_distr (denotation_untyped (Seq b a) m)" by auto
  hence ba_0: "ennreal_Rep_distr (denotation_untyped (Seq b a) m) m2 = 0"
    unfolding support_distr_def'' by auto

  show "ennreal_Rep_distr (denotation_untyped (Seq a b) m) m2 = ennreal_Rep_distr (denotation_untyped (Seq b a) m) m2"
    using ab_0 ba_0 by simp
qed



end
