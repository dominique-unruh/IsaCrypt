theory Scratch
imports Procs_Typed Rewrite Hoare_Typed Hoare_Tactics Lang_Simplifier
(* keywords "module" :: thy_decl
     and "end_module" :: thy_decl *)
begin

(** Development of the line-swapping code **)



(*
lemma program_untyped_readonly_def': 
  "program_untyped_readonly X c = (\<forall>m. hoare_untyped (\<lambda>m'. \<forall>x\<in>X. Rep_memory m x = Rep_memory m' x) c (\<lambda>m'. \<forall>x\<in>X. Rep_memory m x = Rep_memory m' x))"

find_theorems program_untyped_readonly hoare_untyped
*)

lemma seq_swap_untyped:
  fixes A B R
  assumes a_ro: "program_untyped_readonly R a"
  assumes b_ro: "program_untyped_readonly R b"
  assumes foot_a: "program_untyped_footprint A a"
  assumes foot_b: "program_untyped_footprint B b"
  assumes ABR: "A\<inter>B\<subseteq>R"
  shows "denotation_untyped (Seq a b) m = denotation_untyped (Seq b a) m"
apply (subst ereal_Rep_distr_inject[symmetric], rule ext, rename_tac m2)
proof (case_tac "\<forall>x\<in>R. Rep_memory m x = Rep_memory m2 x")
  fix m2 assume same_R: "\<forall>x\<in>R. Rep_memory m x = Rep_memory m2 x"
  def aa == "(\<lambda>m. ereal_Rep_distr (denotation_untyped a m))"
  def bb == "(\<lambda>m. ereal_Rep_distr (denotation_untyped b m))"

  have aa_pos [simp]: "\<And>x y. aa x y \<ge> 0"
    by (simp add: aa_def) 
  have bb_pos [simp]: "\<And>x y. bb x y \<ge> 0"
    by (simp add: bb_def) 

  def A' == "A-R"
  def B' == "-A-R"
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

  have seq_a_b: "ereal_Rep_distr (denotation_untyped (Seq a b) m) m2 = aa m (memory_combine A' m2 m) * bb (memory_combine A' m2 m) m2"
  proof -
    have seq_distr: "ereal_Rep_distr (denotation_untyped (Seq a b) m) m2 = (\<integral>\<^sup>+m1. aa m m1 * bb m1 m2 \<partial>count_space UNIV)" 
      by (simp add: ereal_Rep_compose_distr aa_def bb_def) 
    let ?mix = "memory_combine A' m2 m"
    {fix m1 consider "m1=?mix" | "aa m m1 * bb m1 m2 = 0" | "m1\<noteq>?mix" and "aa m m1 * bb m1 m2 \<noteq> 0" by auto}
(*     have aux_cases: "\<And>P m1. \<lbrakk> m1=?mix \<Longrightarrow> P; aa m m1 * bb m1 m2 = 0 \<Longrightarrow> P;
                              m1\<noteq>?mix \<Longrightarrow>  aa m m1 * bb m1 m2 \<noteq> 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" by auto *)
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
        using less_eq_ereal_def by auto
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
    show "ereal_Rep_distr (denotation_untyped (Seq a b) m) m2 = aa m ?mix * bb ?mix m2" 
      unfolding seq_distr apply (subst m2_single)
      apply (subst nn_integral_singleton_indicator_countspace)
      using aa_pos bb_pos by auto
  qed

  have seq_b_a: "ereal_Rep_distr (denotation_untyped (Seq b a) m) m2 = bb m (memory_combine B' m2 m) * aa (memory_combine B' m2 m) m2" 
  proof -
    have seq_distr: "ereal_Rep_distr (denotation_untyped (Seq b a) m) m2 = (\<integral>\<^sup>+m1. bb m m1 * aa m1 m2 \<partial>count_space UNIV)" 
      by (simp add: ereal_Rep_compose_distr aa_def bb_def) 
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
        using less_eq_ereal_def by auto
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
    show "ereal_Rep_distr (denotation_untyped (Seq b a) m) m2 = bb m ?mix * aa ?mix m2" 
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

  show "ereal_Rep_distr (denotation_untyped (Seq a b) m) m2 = ereal_Rep_distr (denotation_untyped (Seq b a) m) m2"
    unfolding seq_a_b seq_b_a aa_rw bb_rw by (simp add: mult.commute) 
next
  fix m2 assume notsame_R: "\<not> (\<forall>x\<in>R. Rep_memory m x = Rep_memory m2 x)"
  def aa == "(\<lambda>m. ereal_Rep_distr (denotation_untyped a m))"
  def bb == "(\<lambda>m. ereal_Rep_distr (denotation_untyped b m))"

  def eq == "\<lambda>m'. \<forall>x\<in>R. memory_lookup_untyped m' x = memory_lookup_untyped m x"
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
  hence ab_0: "ereal_Rep_distr (denotation_untyped (Seq a b) m) m2 = 0"
    unfolding support_distr_def'' by auto

  have hoareba: "hoare_untyped eq (Seq b a) eq"
    using hoareb hoarea by (rule Hoare_Untyped.seq_rule)
  have "eq m" unfolding eq_def by simp
  with hoareba have "m2 \<in> support_distr (denotation_untyped (Seq b a) m) \<Longrightarrow> eq m2"
    unfolding hoare_untyped_hoare_denotation hoare_denotation_def by simp
  with not_eq have "m2 \<notin> support_distr (denotation_untyped (Seq b a) m)" by auto
  hence ba_0: "ereal_Rep_distr (denotation_untyped (Seq b a) m) m2 = 0"
    unfolding support_distr_def'' by auto

  show "ereal_Rep_distr (denotation_untyped (Seq a b) m) m2 = ereal_Rep_distr (denotation_untyped (Seq b a) m) m2"
    using ab_0 ba_0 by simp
qed


lemma readonly_hoare:
  shows "program_readonly X c = (\<forall>a. hoare {\<forall>x\<in>X. memory_lookup_untyped &m x = a x} \<guillemotleft>c\<guillemotright> {\<forall>x\<in>X. memory_lookup_untyped &m x = a x})"
using denotation_def hoare_untyped program_readonly_def program_untyped_readonly_def readonly_hoare_untyped by auto


lemma seq_swap:
  fixes A B R
  assumes a_ro: "program_readonly R a"
  assumes b_ro: "program_readonly R b"
  assumes foot_a: "program_footprint A a"
  assumes foot_b: "program_footprint B b"
  assumes ABR: "A\<inter>B\<subseteq>R"
  shows "denotation (seq a b) = denotation (seq b a)"
unfolding denotation_def apply simp apply (rule seq_swap_untyped[THEN ext])
using assms
unfolding program_readonly_def program_untyped_readonly_def denotation_def program_footprint_def program_untyped_footprint_def
by auto




lemma program_readonly_write_vars: "program_readonly (- set(write_vars p)) p"
  using program_untyped_readonly_write_vars[of "Rep_program p"]
  unfolding program_readonly_def program_untyped_readonly_def write_vars_def denotation_def 
  by assumption

lemma memory_combine_twice_right [simp]:
  "memory_combine X m1 (memory_combine X m2 m3) = memory_combine X m1 m3"
  unfolding Rep_memory_inject[symmetric] by auto
lemma memory_combine_twice_left [simp]:
  "memory_combine X (memory_combine X m1 m2) m3 = memory_combine X m1 m3"
  unfolding Rep_memory_inject[symmetric] by auto

lemma program_untyped_footprint_hoare:  
  assumes obseq: "obs_eq_untyped X X p p"
  assumes ro: "program_untyped_readonly (-X) p"
  shows "program_untyped_footprint X p"
unfolding program_untyped_footprint_def denotation_footprint_def apply auto
proof -
  fix m1 m1' z assume m1m1'_match: "memory_combine X default m1 = memory_combine X default m1'"
  def f == "\<lambda>m. if (memory_combine X default m = memory_combine X default m1) 
                then memory_combine X m z
                else (if (memory_combine X default m = memory_combine X default z) then memory_combine X m m1 else m)"

  {fix m consider "memory_combine X default m = memory_combine X default m1" and
                  "memory_combine X default m = memory_combine X default z"
                | "memory_combine X default m \<noteq> memory_combine X default m1" and
                  "memory_combine X default m = memory_combine X default z"
                | "memory_combine X default m = memory_combine X default m1" and
                  "memory_combine X default m \<noteq> memory_combine X default z"
                | "memory_combine X default m \<noteq> memory_combine X default m1" and
                  "memory_combine X default m \<noteq> memory_combine X default z" by atomize_elim auto}
  then have ff: "f (f m) = m" for m
  proof (cases m)
  case 1
    have m1: "x \<notin> X \<Longrightarrow> memory_lookup_untyped m1 x = memory_lookup_untyped m x" for x
      using 1 unfolding Rep_memory_inject[symmetric] by (auto, metis)
    have z: "x \<notin> X \<Longrightarrow> memory_lookup_untyped z x = memory_lookup_untyped m x" for x
      using 1 unfolding Rep_memory_inject[symmetric] by (auto, metis)
    have "f m = memory_combine X m z"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      unfolding f_def using m1 by (simp_all add: 1)
    also have "memory_combine X m z = m"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      using z by simp_all
    finally show ?thesis by simp
  next case 2
    have z: "x \<notin> X \<Longrightarrow> memory_lookup_untyped z x = memory_lookup_untyped m x" for x
      using 2 unfolding Rep_memory_inject[symmetric] by (auto, metis)
    have m1z: "memory_combine X default z \<noteq> memory_combine X default m1"
      using 2 by simp
    have "f m = memory_combine X m m1"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      unfolding f_def by (auto simp: m1z 2)
    also have "f (memory_combine X m m1) = memory_combine X m z"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      unfolding f_def by (auto simp: m1z 2)
    also have "memory_combine X m z = m"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      unfolding f_def by (auto simp: z 2)
    finally show ?thesis by assumption
  next case 3
    have m1: "x \<notin> X \<Longrightarrow> memory_lookup_untyped m1 x = memory_lookup_untyped m x" for x
      using 3 unfolding Rep_memory_inject[symmetric] by (auto, metis)
    have m1z: "memory_combine X default z \<noteq> memory_combine X default m1"
      using 3 by simp
    have "f m = memory_combine X m z"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      unfolding f_def by (auto simp: 3)
    also have "f (memory_combine X m z) = memory_combine X m m1"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      unfolding f_def by (auto simp: m1z 3)
    also have "memory_combine X m m1 = m"
      unfolding Rep_memory_inject[symmetric]
      apply (rule ext, rename_tac x, case_tac "x\<in>X")
      using m1 by simp_all
    finally show ?thesis by simp
  next case 4
    have "f m = m"
      unfolding Rep_memory_inject[symmetric] 
      unfolding f_def by (simp add: 4)
    then show ?thesis by simp
  qed
  
  def m2 == "f m1"
  def eqX == "\<lambda>m1 m2. \<forall>x\<in>X. Rep_memory m1 x = Rep_memory m2 x"
  have "rhoare_untyped eqX p p eqX"
    using obseq unfolding obs_eq_untyped_def eqX_def by simp
  moreover have "eqX m1 m2"
    by (simp add: eqX_def f_def m2_def)
  ultimately obtain \<mu> where fst\<mu>: "apply_to_distr fst \<mu> = denotation_untyped p m1"
                      and snd\<mu>: "apply_to_distr snd \<mu> = denotation_untyped p m2"
                      and supp\<mu>: "\<And>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<Longrightarrow> eqX m1' m2'"
    unfolding rhoare_untyped_rhoare_denotation rhoare_denotation_def apply atomize_elim by auto
  have "\<forall>m1'\<in>support_distr (denotation_untyped p m1). memory_combine X default m1' = memory_combine X default m1"
    apply (subst Rep_memory_inject[symmetric])
    using ro unfolding program_untyped_readonly_def denotation_readonly_def by auto
  then have supp\<mu>1: "\<And>m1' m2'. (m1',m2')\<in>support_distr \<mu> \<Longrightarrow>  memory_combine X default m1' = memory_combine X default m1"
    by (metis fst\<mu> fst_conv image_eqI support_apply_to_distr)
  have supp\<mu>2': "\<forall>m2'\<in>support_distr (denotation_untyped p m2). memory_combine X default m2' = memory_combine X default m2"
    apply (subst Rep_memory_inject[symmetric])
    using ro unfolding program_untyped_readonly_def denotation_readonly_def by auto
  have supp\<mu>2: "(m1',m2')\<in>support_distr \<mu>
        \<Longrightarrow>  memory_combine X default m2' = memory_combine X default m2" for m1' m2'
  proof -
    assume "(m1',m2')\<in>support_distr \<mu>"
    hence "m2' \<in> support_distr (apply_to_distr snd \<mu>)"
      by force 
    hence "m2' \<in> support_distr (denotation_untyped p m2)" using snd\<mu> by auto
    thus ?thesis using supp\<mu>2' by simp
  qed
  have m2z: "memory_combine X default m2 = memory_combine X default z"
    unfolding m2_def f_def apply (subst Rep_memory_inject[symmetric])+ by auto
  have supp\<mu>_f: "(m1',m2')\<in>support_distr \<mu> \<Longrightarrow> m2' = f m1'" for m1' m2'
  proof -
    assume supp: "(m1',m2')\<in>support_distr \<mu>"
    have t1: "x\<in>X \<Longrightarrow> memory_lookup_untyped m1' x = memory_lookup_untyped m2' x" for x
      using supp\<mu> supp eqX_def by simp
    have "memory_combine X default m1' = memory_combine X default m1"
      using supp\<mu>1 supp by simp
    hence t2: "x\<notin>X \<Longrightarrow> Rep_memory m1' x = Rep_memory m1 x" for x
      unfolding Rep_memory_inject[symmetric] by (auto, metis)
    have "memory_combine X default m2' = memory_combine X default z"
      using supp\<mu>2 supp m2z by simp
    hence t3: "x\<notin>X \<Longrightarrow> Rep_memory m2' x = Rep_memory z x" for x
      unfolding Rep_memory_inject[symmetric] by (auto, metis)
    show ?thesis
      unfolding Rep_memory_inject[symmetric] f_def
      using t1 t2 t3 by (auto, metis)
  qed
  def \<mu>' == "apply_to_distr (\<lambda>(m1',m2'). (m1',f m2')) \<mu>"
  have "\<And>m1' m2'. (m1',m2')\<in>support_distr \<mu>' \<Longrightarrow> m2' = m1'" 
    unfolding \<mu>'_def using supp\<mu>_f ff by auto 
  then have \<mu>'eq: "apply_to_distr fst \<mu>' = apply_to_distr snd \<mu>'"
    by (metis apply_to_distr_cong prod.collapse)
  
  have "denotation_untyped p m1 = apply_to_distr fst \<mu>"
    by (simp add: fst\<mu>)
  also have "\<dots> = apply_to_distr fst \<mu>'"
    unfolding \<mu>'_def apply simp
    apply (rewrite at "\<lambda>x. fst (case x of (m1',m2') \<Rightarrow> (m1',f m2'))" to fst   eq_reflection)
    by auto
  also have "\<dots> = apply_to_distr snd \<mu>'" 
    by (simp add: \<mu>'eq)
  also have "\<dots> = apply_to_distr f (apply_to_distr snd \<mu>)"
    unfolding \<mu>'_def apply simp
    apply (rewrite at "\<lambda>x. snd (case x of (m1',m2') \<Rightarrow> (m1',f m2'))" to "\<lambda>x. f (snd x)"  eq_reflection)
    by auto
  also have "\<dots> = apply_to_distr f (denotation_untyped p m2)"
    by (simp add: snd\<mu>)
  finally have "denotation_untyped p m1 = apply_to_distr f (denotation_untyped p m2)" by assumption
  
  then have "Rep_distr (denotation_untyped p m1) m1' = Rep_distr (apply_to_distr f (denotation_untyped p m2)) m1'" 
    unfolding Rep_distr_inject[symmetric] by simp
  also have "\<dots> = Rep_distr (denotation_untyped p m2) (f m1')"
    apply (rule Rep_apply_distr_biject) by (fact ff)+
  also have "m2 = memory_combine X m1 z"
    unfolding m2_def f_def apply (subst Rep_memory_inject[symmetric])+ by auto
  also have "f m1' = memory_combine X m1' z"
    unfolding f_def apply (subst Rep_memory_inject[symmetric])+ using m1m1'_match by auto
  finally show "Rep_distr (denotation_untyped p m1) m1' =
                Rep_distr (denotation_untyped p (memory_combine X m1 z)) (memory_combine X m1' z)" by assumption
next
  fix m m' assume "memory_combine X default m \<noteq> memory_combine X default m'"
  then show "Rep_distr (denotation_untyped p m) m' = 0" (* TODO remove ereal, change support_distr_def'' *)
    using ro unfolding program_untyped_readonly_def denotation_readonly_def support_distr_def'''
    apply (subst (asm) Rep_memory_inject[symmetric]) by auto 
qed

lemma program_untyped_footprint_vars: "program_untyped_footprint (set(vars_untyped p)) p"
proof -
  have "obs_eq_untyped (set(vars_untyped p)) (set(vars_untyped p)) p p"
    by (simp add: self_obseq_vars)
  moreover have "program_untyped_readonly (- set(vars_untyped p)) p"
    by (meson Compl_anti_mono denotation_readonly_def program_untyped_readonly_def program_untyped_readonly_write_vars subsetCE write_vars_subset_vars_untyped(1))
  ultimately show ?thesis
    by (rule program_untyped_footprint_hoare)
qed

lemma program_footprint_vars: "program_footprint (set(vars p)) p"
  using program_untyped_footprint_vars
  unfolding program_footprint_def program_untyped_footprint_def vars_def denotation_def.


lemma seq_swap2:
  assumes "set (vars a) \<inter> set (write_vars b) = {}"
  assumes "set (vars b) \<inter> set (write_vars a) = {}"
  shows "denotation (seq a b) = denotation (seq b a)"
proof -
  def A == "set(vars a)"
  def B == "set(vars b)"
  def R == "UNIV - set(write_vars a) - set(write_vars b)"
  have "program_readonly R a"
    using R_def denotation_readonly_def program_readonly_def program_readonly_write_vars by auto
  moreover have "program_readonly R b"
    using R_def denotation_readonly_def program_readonly_def program_readonly_write_vars by auto
  moreover have "program_footprint A a"
    using A_def program_footprint_vars by auto
  moreover have "program_footprint B b"
    using B_def program_footprint_vars by auto
  moreover have ABR: "A\<inter>B\<subseteq>R"
    unfolding A_def B_def R_def using assms by auto
  ultimately show ?thesis
    by (rule seq_swap)
qed    



lemma denotation_eq_seq_snd:
  assumes "denotation b = denotation b'"
  shows "denotation (seq a b) = denotation (seq a b')"
unfolding denotation_seq[THEN ext] using assms by simp
    
lemma denotation_eq_seq_fst:
  assumes "denotation a = denotation a'"
  shows "denotation (seq a b) = denotation (seq a' b)"
unfolding denotation_seq[THEN ext] using assms by simp
    
ML {*

fun split_with_seq_tac ctx n =
  if n=0 then resolve_tac ctx @{thms denotation_seq_skip[symmetric]} 
  else if n<0 then error "split_with_seq_tac: n<0"
  else
  SUBGOAL (fn (goal,i) => 
  let
      val concl = Logic.strip_assums_concl goal
      val lhsprog = Hoare_Tactics.dest_denotation (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop concl)))
      val proglen = Hoare_Tactics.program_length lhsprog
      val n' = Thm.cterm_of ctx (Hoare_Tactics.mk_suc_nat (proglen - n))
      val insert_split_n = Drule.infer_instantiate' ctx [SOME n'] @{thm insert_split}
  in
    resolve_tac ctx [insert_split_n] i  
    THEN Raw_Simplifier.rewrite_goal_tac ctx @{thms split_program_simps} i
  end)

*}

ML {*
fun extract_range_tac _   ([],_)   = error "empty range given"
  | extract_range_tac ctx ([a],len) =
      split_with_seq_tac ctx (a-1)
      THEN' resolve_tac ctx @{thms denotation_eq_seq_snd}
      THEN' split_with_seq_tac ctx len
      THEN' resolve_tac ctx @{thms denotation_eq_seq_fst}
  | extract_range_tac _   (_::_::_,_) = error "extract_range_tac: extracting nested ranges not supported"
*}

thm seq_swap

ML {* open Tools *}

ML {*
fun procedure_info_varseteq_tac ctx =
  CONVERSION (Procs_Typed.procedure_info_conv false ctx)
  THEN'
  ASSERT_SOLVED' (simp_tac ctx)
         (fn subgoal1 => fn subgoals => 
            raise TERM("In procedure_info_varseteq_tac, I got subgoal (1).\n"^
                       "I could not prove that subgoal using simp_tac.\n",
                         subgoal1::subgoals))
*}

ML {*
fun swap_tac ctx range len1 i (*(A,B,R)*) =
  extract_range_tac ctx range i
  THEN split_with_seq_tac ctx len1 i
  THEN resolve_tac ctx @{thms seq_swap2} i
  THEN (simp_tac ctx THEN_ALL_NEW procedure_info_varseteq_tac ctx) (i+1)
  THEN (simp_tac ctx THEN_ALL_NEW procedure_info_varseteq_tac ctx) i
*}

procedure f where "f = LOCAL x. proc () { x := (1::int); return () }"

procedure g where "g = LOCAL x. proc () { x := call f(); return () }"

lemma
  assumes "LOCAL c3 c4 c5 (x::int variable). hoare {P &m} \<guillemotleft>c1\<guillemotright>; \<guillemotleft>c2\<guillemotright>; c4:=call f(); c5:=x; c3:=x; \<guillemotleft>c6\<guillemotright> {Q &m}"
  shows   "LOCAL c3 c4 c5 (x::int variable). hoare {P &m} \<guillemotleft>c1\<guillemotright>; \<guillemotleft>c2\<guillemotright>; c3:=x; c4:=call f(); c5:=x; \<guillemotleft>c6\<guillemotright> {Q &m}"
apply (rule denotation_eq_rule)
apply (tactic \<open>swap_tac @{context} ([3],3) 1 1\<close>)
(* close (simp; tactic \<open>CONVERSION (Procs_Typed.procedure_info_conv false @{context}) 1\<close>; simp; tactic \<open>no_tac\<close>) *)
(* close (simp; tactic \<open>CONVERSION (Procs_Typed.procedure_info_conv false @{context}) 1\<close>; simp; tactic \<open>no_tac\<close>) *)
apply simp
by (fact assms)










end
