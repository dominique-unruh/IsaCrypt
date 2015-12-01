theory Scratch
imports Procs_Typed Rewrite Hoare_Typed Hoare_Tactics Lang_Simplifier
keywords "module" :: thy_decl
     and "end_module" :: thy_decl
begin

definition "memory_combine X m1 m2 = Abs_memory (\<lambda>x. if x\<in>X then Rep_memory m1 x else Rep_memory m2 x)"
lemma Rep_memory_combine [simp]: "Rep_memory (memory_combine X m1 m2) = (\<lambda>x. if x\<in>X then Rep_memory m1 x else Rep_memory m2 x)"
  unfolding memory_combine_def apply (subst Abs_memory_inverse) using Rep_memory by auto

instantiation memory :: default begin
definition "default = Abs_memory (\<lambda>x. t_default (vu_type x))"
instance ..
end

lemma Rep_memory_default [simp]: "Rep_memory default = (\<lambda>x. t_default (vu_type x))"
  unfolding default_memory_def apply (subst Abs_memory_inverse) by auto
definition "restrict_memory X m = memory_combine X m default"

definition "denotation_footprint X d = (\<forall>m m' z. Rep_distr (d m) m' 
    = Rep_distr (d (memory_combine X m z)) (memory_combine X m' z) 
      * (if memory_combine X default m = memory_combine X default m' then 1 else 0))"
lemma denotation_footprint_mono:
  assumes mono: "A \<ge> B"
  assumes foot: "denotation_footprint B d"
  shows "denotation_footprint A d"
proof (unfold denotation_footprint_def, (rule allI)+)
  fix m m' z
  def dd == "\<lambda>m. Rep_distr (d m)"
(*  have "\<And>m m' z. dd m m' = dd (memory_combine B m z) (memory_combine B m' z) 
      * (if memory_combine B default m = memory_combine B default m' then 1 else 0)"
    using foot unfolding denotation_footprint_def dd_def by simp*)
  def z' == "memory_combine A m z"
  have dd1: "dd m m' = dd (memory_combine B m z') (memory_combine B m' z') 
      * (if memory_combine B default m = memory_combine B default m' then 1 else 0)"
    using foot unfolding denotation_footprint_def dd_def by simp
  have comb1: "memory_combine B m z' = memory_combine A m z"
    unfolding z'_def apply (rule Rep_memory_inject[THEN iffD1])
    unfolding Rep_memory_combine apply (rule ext) using mono by auto
  have comb2: "memory_combine B default m = memory_combine B default m' \<Longrightarrow> memory_combine B m' z' = memory_combine A m' z"
    unfolding z'_def apply (subst (asm) Rep_memory_inject[symmetric])
    apply (subst Rep_memory_inject[symmetric]) 
    unfolding Rep_memory_combine apply (rule ext) using mono apply auto by meson
  have dd2: "dd m m' = dd (memory_combine A m z) (memory_combine A m' z) 
      * (if memory_combine B default m = memory_combine B default m' then 1 else 0)"
    using dd1 comb1 comb2 by auto
  have "dd m m' = dd (memory_combine A m z) (memory_combine A m' z) 
      * (if memory_combine A default m = memory_combine A default m' then 1 else 0)"
  proof (cases "memory_combine A default m = memory_combine A default m'", 
         cases "memory_combine B default m = memory_combine B default m'")
    assume "memory_combine B default m = memory_combine B default m'" and "memory_combine A default m = memory_combine A default m'"
    thus ?thesis using dd2 by auto
  next
    assume Aneq: "memory_combine A default m \<noteq> memory_combine A default m'"
    then obtain x where x: "(if x \<in> A then Rep_memory default x else Rep_memory m x) \<noteq> (if x \<in> A then Rep_memory default x else Rep_memory m' x)"
      apply (subst (asm) Rep_memory_inject[symmetric]) by auto
    hence "x \<notin> A" by auto
    with mono have "x\<notin>B" by auto
    have "memory_combine B default m \<noteq> memory_combine B default m'"
      apply (subst Rep_memory_inject[symmetric], simp)
      apply (subst fun_eq_iff, auto, rule exI[of _ x])
      using `x\<notin>B` `x\<notin>A` x by simp
    with Aneq show ?thesis using dd2 by auto
  next
    assume Aeq: "memory_combine A default m = memory_combine A default m'"
    hence Aeq': "\<And>x. x\<notin>A \<Longrightarrow> Rep_memory m x = Rep_memory m' x"
      apply (subst (asm) Rep_memory_inject[symmetric]) apply auto by metis
    assume Bneq: "memory_combine B default m \<noteq> memory_combine B default m'"
    then obtain  x where x: "(if x \<in> B then Rep_memory default x else Rep_memory m x) \<noteq> (if x \<in> B then Rep_memory default x else Rep_memory m' x)"
      apply (subst (asm) Rep_memory_inject[symmetric]) by auto
    hence "x \<notin> B" by auto
    with x have Bneq': "Rep_memory m x \<noteq> Rep_memory m' x" by auto
    hence "x \<in> A" using Aeq' by auto
    have dd_0: "dd m m' = 0"
      unfolding dd1 using Bneq by simp
    have neq: "memory_combine B default (memory_combine A m z) \<noteq> memory_combine B default (memory_combine A m' z)"
      apply (subst Rep_memory_inject[symmetric], auto)
      apply (drule fun_eq_iff[THEN iffD1]) apply (drule spec[of _ x])
      using `x\<notin>B` `x\<in>A` Bneq' by auto
    have "dd (memory_combine A m z) (memory_combine A m' z) = dd (memory_combine B (memory_combine A m z) xxx) (memory_combine B (memory_combine A m' z) xxx)
        * (if memory_combine B default (memory_combine A m z) = memory_combine B default (memory_combine A m' z) then 1 else 0)"
      using foot unfolding denotation_footprint_def dd_def by auto 
    hence "dd (memory_combine A m z) (memory_combine A m' z) = 0"
      using neq by auto
    with dd_0 show ?thesis by simp
  qed
  thus "Rep_distr (d m) m' =
       Rep_distr (d (memory_combine A m z)) (memory_combine A m' z) *
       (if memory_combine A default m = memory_combine A default m' then 1\<Colon>real else (0\<Colon>real))"
    unfolding dd_def by simp
qed

definition "program_untyped_footprint X c = denotation_footprint X (denotation_untyped c)"
lemma program_untyped_footprint_mono:
  assumes mono: "A \<ge> B"
  assumes foot: "program_untyped_footprint B d"
  shows "program_untyped_footprint A d"
using assms unfolding program_untyped_footprint_def by (rule denotation_footprint_mono)

definition "program_footprint X c = denotation_footprint X (denotation c)"

definition "denotation_readonly X d = (\<forall>m. \<forall>m'\<in>support_distr (d m). \<forall>x\<in>X. Rep_memory m x = Rep_memory m' x)"
definition "program_readonly X c = denotation_readonly X (denotation c)"
definition "program_untyped_readonly X c = denotation_readonly X (denotation_untyped c)"

lemma readonly_hoare_untyped:
  shows "program_untyped_readonly X c = (\<forall>a. hoare_untyped (\<lambda>m. \<forall>x\<in>X. memory_lookup_untyped m x = a x) c (\<lambda>m. \<forall>x\<in>X. memory_lookup_untyped m x = a x))"
unfolding program_untyped_readonly_def hoare_untyped_hoare_denotation hoare_denotation_def denotation_readonly_def memory_lookup_untyped_def
by metis

lemma readonly_hoare:
  shows "program_readonly X c = (\<forall>a. hoare {\<forall>x\<in>X. memory_lookup_untyped &m x = a x} \<guillemotleft>c\<guillemotright> {\<forall>x\<in>X. memory_lookup_untyped &m x = a x})"
using denotation_def hoare_untyped program_readonly_def program_untyped_readonly_def readonly_hoare_untyped by auto



lemma denotation_footprint_readonly:
  assumes RX: "R\<inter>X={}"
  assumes foot: "denotation_footprint X d"
  shows "denotation_readonly R d"
proof (auto simp: denotation_readonly_def)
  fix m m' x assume "x\<in>R" assume "m' \<in> support_distr (d m)"
  hence "Rep_distr (d m) m' \<noteq> 0" by (simp add: support_distr_def)
  hence "Rep_distr (d (memory_combine X m z)) (memory_combine X m' z) 
      * (if memory_combine X default m = memory_combine X default m' then 1 else 0) \<noteq> 0"
    using assms(2) denotation_footprint_def by auto
  hence "memory_combine X default m = memory_combine X default m'" by (metis (full_types) mult_zero_right)
  thus "Rep_memory m x = Rep_memory m' x"
    by (metis (full_types) Rep_memory_combine `x\<in>R` assms(1) disjoint_iff_not_equal)
qed
(*proof (rule ccontr)
  assume "\<not> denotation_readonly R d"
  then obtain x m m' where neq: "Rep_memory m x \<noteq> Rep_memory m' x" and pos: "Rep_distr (d m) m' > 0" and "x\<in>R"
    unfolding denotation_readonly_def support_distr_def by auto
  from `x\<in>R` have "x\<notin>X" using RX by auto
  with neq have neqX: "memory_combine X default m \<noteq> memory_combine X default m'"
    apply (subst Rep_memory_inject[symmetric]) apply auto by metis
  fix z
  from foot have "Rep_distr (d m) m' = Rep_distr (d (memory_combine X m z)) (memory_combine X m' z) *
     (if memory_combine X default m = memory_combine X default m' then 1 else 0)"
    unfolding denotation_footprint_def by auto
  hence "Rep_distr (d m) m' = 0"
    using neqX by auto
  with pos show False by simp
qed*)

lemma program_untyped_footprint_readonly:
  assumes "R\<inter>X={}"
  assumes "program_untyped_footprint X d"
  shows "program_untyped_readonly R d"
using assms denotation_footprint_readonly program_untyped_footprint_def program_untyped_readonly_def by auto

lemma program_footprint_readonly:
  assumes "R\<inter>X={}"
  assumes "program_footprint X d"
  shows "program_readonly R d"
using assms denotation_footprint_readonly program_footprint_def program_readonly_def by auto

lemma denotation_readonly_union:
  assumes "denotation_readonly X c"
  assumes "denotation_readonly Y c"
  shows "denotation_readonly (X\<union>Y) c"
using assms unfolding denotation_readonly_def
by auto

lemma program_untyped_readonly_union:
  assumes "program_untyped_readonly X c"
  assumes "program_untyped_readonly Y c"
  shows "program_untyped_readonly (X\<union>Y) c"
using assms unfolding program_untyped_readonly_def
by (rule denotation_readonly_union)




lemma seq_swap_untyped:
  fixes A B R
  assumes a_ro: "program_untyped_readonly R a"
  assumes b_ro: "program_untyped_readonly R b"
  assumes foot_a: "program_untyped_footprint A a"
  assumes foot_b: "program_untyped_footprint B b"
  assumes ABR: "A\<inter>B\<subseteq>R"
  shows "denotation_untyped (Seq a b) m = denotation_untyped (Seq b a) m"
proof -
  def aa == "(\<lambda>m. Rep_distr (denotation_untyped a m))"
  def bb == "(\<lambda>m. Rep_distr (denotation_untyped b m))"
  have aa_pos: "\<And>x y. aa x y \<ge> 0"
    by (simp add: Rep_distr_geq0 aa_def) 
  have bb_pos: "\<And>x y. bb x y \<ge> 0"
    by (simp add: Rep_distr_geq0 bb_def) 
  have aux: "\<And>x y z. ereal (x * indicator y z) = ereal x * indicator y z"
    by (simp add: ereal_mult_indicator)

  def A' == "A-R"
  def B' == "-A-R"
  have A'RB': "(A'\<union>R) = -B'" unfolding A'_def B'_def by auto

  (* TODO: which of these have's are used? *)
  have "program_untyped_readonly B' a"
    apply (rule program_untyped_footprint_readonly)
    defer close (fact foot_a)
    unfolding B'_def by auto
  hence "program_untyped_readonly (B'\<union>R) a"
    using a_ro unfolding program_untyped_readonly_def
    by (rule denotation_readonly_union)
    
  have "program_untyped_readonly A' b"
    apply (rule program_untyped_footprint_readonly)
    defer close (fact foot_b)
    unfolding A'_def using ABR by auto

  have "program_untyped_readonly (A'\<union>R) b"
    apply (rewrite at "A'\<union>R" to "(A-R)\<union>R" eq_reflection)
     close (simp add: A'_def)
    apply (rule program_untyped_readonly_union)
    apply (rule program_untyped_footprint_readonly)
      defer close (fact foot_b) close (fact b_ro)
    using ABR by auto

  have "program_untyped_footprint (A'\<union>R) a"
    apply (rule program_untyped_footprint_mono) defer apply (fact foot_a)
    unfolding A'_def by simp

  have "program_untyped_footprint (B'\<union>R) b"
    apply (rule program_untyped_footprint_mono) defer apply (fact foot_b)
    unfolding B'_def using ABR by auto

  have "\<And>m2. Rep_distr (denotation_untyped (Seq a b) m) m2 = aa m (memory_combine A' m2 m) * bb (memory_combine A' m2 m) m2" 
  proof -
    fix m2
    have seq_distr: "Rep_distr (denotation_untyped (Seq a b) m) m2 = real (\<integral>\<^sup>+m1. ereal (aa m m1 * bb m1 m2) \<partial>count_space UNIV)" 
      by (simp add: compose_Rep_distr aa_def bb_def) 
    let ?mix = "memory_combine A' m2 m"
    have aux_cases: "\<And>P m1. \<lbrakk> m1=?mix \<Longrightarrow> P; aa m m1 * bb m1 m2 = 0 \<Longrightarrow> P;
                              m1\<noteq>?mix \<Longrightarrow>  aa m m1 * bb m1 m2 \<noteq> 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" by auto
    have m2_single: "\<And>m1. aa m m1 * bb m1 m2 = aa m m1 * bb m1 m2 * indicator {?mix} m1"
    proof (rule aux_cases)
      fix m1 assume "m1=?mix" thus "?thesis m1" by simp
    next
      fix m1 assume "aa m m1 * bb m1 m2 = 0"
      thus "?thesis m1" by simp
    next
      fix m1 assume "m1\<noteq>?mix" 
      assume "aa m m1 * bb m1 m2 \<noteq> 0"
      with aa_pos bb_pos have aa: "aa m m1 > 0" and bb: "bb m1 m2 > 0" 
        using less_eq_real_def by auto
      have mm1B'R: "\<forall>x\<in>B'\<union>R. Rep_memory m x = Rep_memory m1 x"
        using aa `program_untyped_readonly (B'\<union>R) a` unfolding aa_def program_untyped_readonly_def denotation_readonly_def support_distr_def by auto
      have m1m2A': "\<forall>x\<in>A'. Rep_memory m1 x = Rep_memory m2 x"
        using bb `program_untyped_readonly A' b` unfolding bb_def program_untyped_readonly_def denotation_readonly_def support_distr_def by auto
      have "m1 = ?mix"
        apply (rule Rep_memory_inject[THEN iffD1], rule ext, auto)
         using m1m2A' apply blast
        by (metis A'_def B'_def ComplI Compl_Diff_eq Un_Diff_cancel2 mm1B'R)
      with `m1\<noteq>?mix` show "?thesis m1" by simp
    qed
    show "Rep_distr (denotation_untyped (Seq a b) m) m2 = aa m ?mix * bb ?mix m2" 
      unfolding seq_distr apply (subst m2_single) apply (subst aux)
      apply (subst nn_integral_singleton_indicator_countspace)
      using aa_pos bb_pos by auto
  qed

  moreover
  have "\<And>m2. Rep_distr (denotation_untyped (Seq b a) m) m2 = bb m (memory_combine B' m2 m) * aa (memory_combine B' m2 m) m2" 
  proof -
    fix m2
    have seq_distr: "Rep_distr (denotation_untyped (Seq b a) m) m2 = real (\<integral>\<^sup>+m1. ereal (bb m m1 * aa m1 m2) \<partial>count_space UNIV)" 
      by (simp add: compose_Rep_distr aa_def bb_def) 
    let ?mix = "memory_combine B' m2 m"
    have aux_cases: "\<And>P m1. \<lbrakk> m1=?mix \<Longrightarrow> P; bb m m1 * aa m1 m2 = 0 \<Longrightarrow> P;
                              m1\<noteq>?mix \<Longrightarrow>  bb m m1 * aa m1 m2 \<noteq> 0 \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P" by auto
    have m2_single: "\<And>m1. bb m m1 * aa m1 m2 = bb m m1 * aa m1 m2 * indicator {?mix} m1"
    proof (rule aux_cases)
      fix m1 assume "m1=?mix" thus "?thesis m1" by simp
    next
      fix m1 assume "bb m m1 * aa m1 m2 = 0"
      thus "?thesis m1" by simp
    next
      fix m1 assume "m1\<noteq>?mix" 
      assume "bb m m1 * aa m1 m2 \<noteq> 0"
      with aa_pos bb_pos have bb: "bb m m1 > 0" and aa: "aa m1 m2 > 0" 
        using less_eq_real_def by auto
      have mm1A'R: "\<forall>x\<in>A'\<union>R. Rep_memory m x = Rep_memory m1 x"
        using bb `program_untyped_readonly (A'\<union>R) b` unfolding bb_def program_untyped_readonly_def denotation_readonly_def support_distr_def by auto
      have m1m2B': "\<forall>x\<in>B'. Rep_memory m1 x = Rep_memory m2 x"
        using aa `program_untyped_readonly B' a` unfolding aa_def program_untyped_readonly_def denotation_readonly_def support_distr_def by auto
      have "m1 = ?mix"
        apply (rule Rep_memory_inject[THEN iffD1], rule ext, auto)
         using m1m2B' apply blast
          by (metis A'_def B'_def DiffI UNIV_I UnI1 UnI2 mm1A'R)
      with `m1\<noteq>?mix` show "?thesis m1" by simp
    qed
    show "Rep_distr (denotation_untyped (Seq b a) m) m2 = bb m ?mix * aa ?mix m2" 
      unfolding seq_distr apply (subst m2_single) apply (subst aux)
      apply (subst nn_integral_singleton_indicator_countspace)
      using aa_pos bb_pos by auto
  qed

  have aux: "\<And>X m m'. (memory_combine X default m = memory_combine X default m') = (\<forall>x\<in>-X. Rep_memory m x = Rep_memory m' x)"
    apply (subst Rep_memory_inject[symmetric]) apply auto apply metis by (meson ComplI) 

  have foot_aux_a: "\<And>m m' z. aa m m' =
       aa (memory_combine (A'\<union>R) m z) (memory_combine (A'\<union>R) m' z) *
       (if memory_combine (A'\<union>R) default m = memory_combine (A'\<union>R) default m' then 1 else 0)"
    using `program_untyped_footprint (A'\<union>R) a` 
    unfolding aa_def program_untyped_footprint_def denotation_footprint_def by simp
    


  moreover
  have "\<And>m2. \<forall>x\<in>B'. Rep_memory m2 x = Rep_memory m x \<Longrightarrow> aa m (memory_combine A' m2 m) = aa (memory_combine B' m2 m) m2" 
  proof (case_tac "\<forall>x\<in>R. Rep_memory m2 x = Rep_memory m x")
    fix m2 assume asm: "\<forall>x\<in>B'. Rep_memory m2 x = Rep_memory m x"
    assume asmR: "\<forall>x\<in>R. Rep_memory m2 x = Rep_memory m x"
    have l1: "memory_combine (-B') m m2 = memory_combine (-B') (memory_combine B' m2 m) m" 
      apply (rule Rep_memory_inject[THEN iffD1])
      apply (rule fun_eq_iff[THEN iffD2])
      using asm by auto
    have l2: "memory_combine (- B') (memory_combine A' m2 m) m2 = memory_combine (- B') m2 m"
      apply (rule Rep_memory_inject[THEN iffD1])
      apply (rule fun_eq_iff[THEN iffD2])
      using asm A'RB' asmR by fastforce
      
    show "aa m (memory_combine A' m2 m) = aa (memory_combine B' m2 m) m2" 
      apply (subst foot_aux_a[where z1=m2])
      apply (subst (2) foot_aux_a[where z1=m])
      apply (subst aux)+ 
      unfolding A'RB' unfolding l1[symmetric] l2 
      apply auto using asm by force
  next
    fix m2 assume asm: "\<not> (\<forall>x\<in>R. Rep_memory m2 x = Rep_memory m x)"
    then obtain x where "x\<in>R" and "Rep_memory m2 x \<noteq> Rep_memory m x" by auto
(*lhs,rhs=0 because aa readonly*)
    show "aa m (memory_combine A' m2 m) = aa (memory_combine B' m2 m) m2" 
      by later
  qed

  moreover
  have "\<And>m2. bb (memory_combine A' m2 m) m2 = bb m (memory_combine B' m2 m)" by later

  ultimately have "\<And>m2. Rep_distr (denotation_untyped (Seq a b) m) m2 = Rep_distr (denotation_untyped (Seq b a) m) m2"
    by simp
  thus "?thesis"
    by (rule_tac Rep_distr_inject[THEN iffD1], auto)
qed

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

(* TODO move Lang_Untyped *)
fun write_vars_untyped :: "program_rep \<Rightarrow> variable_untyped list" 
and write_vars_proc_untyped :: "procedure_rep \<Rightarrow> variable_untyped list" where
  "write_vars_untyped Skip = []"
| "write_vars_untyped (Seq p1 p2) = (write_vars_untyped p1) @ (write_vars_untyped p2)"
| "write_vars_untyped (Assign pat e) = pu_vars pat"
| "write_vars_untyped (Sample pat e) = pu_vars pat"
| "write_vars_untyped (IfTE e p1 p2) = write_vars_untyped p1 @ write_vars_untyped p2"
| "write_vars_untyped (While e p) = write_vars_untyped p"
| "write_vars_untyped (CallProc v prc args) = 
      pu_vars v @ write_vars_proc_untyped prc"
| "write_vars_proc_untyped (Proc body pargs ret) =
      [v. v\<leftarrow>pu_vars pargs, vu_global v]
      @ [v. v\<leftarrow>write_vars_untyped body, vu_global v]"
| "write_vars_proc_untyped (ProcRef i) = []"
| "write_vars_proc_untyped (ProcAppl p q) = (write_vars_proc_untyped p) @ (write_vars_proc_untyped q)"
| "write_vars_proc_untyped (ProcAbs p) = write_vars_proc_untyped p"
| "write_vars_proc_untyped (ProcPair p q) = write_vars_proc_untyped p @ write_vars_proc_untyped q"
| "write_vars_proc_untyped (ProcUnpair _ p) = write_vars_proc_untyped p"
definition "write_vars prog = write_vars_untyped (Rep_program prog)"

lemma write_vars_seq [simp]: "write_vars (seq a b) = write_vars a @ write_vars b" by (simp add: write_vars_def)
lemma write_vars_assign [simp]: "write_vars (assign x e) = p_vars x" by (simp add: p_vars_def write_vars_def)
lemma write_vars_sample [simp]: "write_vars (sample x e) = p_vars x" by (simp add: p_vars_def write_vars_def)
lemma write_vars_while [simp]: "write_vars (Lang_Typed.while e p) = write_vars p" by (simp add: write_vars_def)
lemma write_vars_ifte [simp]: "write_vars (Lang_Typed.ifte e p1 p2) = write_vars p1 @ write_vars p2" by (simp add: write_vars_def)
definition "write_vars_proc_global p == [v. v<-p_vars (p_arg p), vu_global v] @ [v. v<-write_vars (p_body p), vu_global v]"
lemma vars_callproc [simp]: "write_vars (callproc x p a) = p_vars x @ write_vars_proc_global p"
  unfolding write_vars_def write_vars_proc_global_def p_vars_def by (auto simp: mk_procedure_untyped_def)
lemma write_vars_skip [simp]: "write_vars Lang_Typed.skip = []" by (simp add: write_vars_def)

lemma denotation_readonly_0 [simp]: "denotation_readonly X (\<lambda>m. 0)"
  unfolding denotation_readonly_def
  by (simp add: support_distr_def)

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
    and "\<And>R. set (write_vars_proc_untyped q) \<inter> R = {} \<Longrightarrow> True" 
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
        (IfTE e p1 p2) (\<lambda>m\<Colon>memory. \<forall>x\<Colon>variable_untyped\<in>R. memory_lookup_untyped m x = a x)"
      apply (rule Hoare_Untyped.if_case_rule) using p1 close simp using p2 by simp
    show ?case
      apply (subst readonly_hoare_untyped, rule allI)
      using t by simp
  next
  case (While e p)
    have p: "\<And>a. hoare_untyped (\<lambda>m. \<forall>x\<in>R. memory_lookup_untyped m x = a x) p (\<lambda>m. \<forall>x\<in>R. memory_lookup_untyped m x = a x)"
      using While.hyps[where R=R] unfolding readonly_hoare_untyped using While.prems by auto
    have p': "\<And>a. hoare_untyped (\<lambda>m. (\<forall>x\<in>R. memory_lookup_untyped m x = a x) \<and> eu_fun e m = embedding True)
        p (\<lambda>m\<Colon>memory. \<forall>x\<Colon>variable_untyped\<in>R. memory_lookup_untyped m x = a x)"
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
      show ?thesis by later
    qed (auto simp: program_untyped_readonly_def denotation_untyped_CallProc_bad[THEN ext])
  next
  case Proc show ?case by simp
  next
  case ProcRef show ?case by simp
  next
  case ProcAbs show ?case by simp
  next
  case ProcAppl show ?case by simp
  next
  case ProcPair show ?case by simp
  next
  case ProcUnpair show ?case by simp
  qed
  thus ?thesis by simp
qed


lemma program_readonly_write_vars: "program_readonly (- set(write_vars p)) p"
SORRY

lemma program_footprint_vars: "program_footprint (set(vars p)) p"
SORRY


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
  if n=0 then rtac @{thm denotation_seq_skip[symmetric]} 
  else if n<0 then error "split_with_seq_tac: n<0"
  else
  SUBGOAL (fn (goal,i) => 
  let
      val concl = Logic.strip_assums_concl goal
      val lhsprog = Hoare_Tactics.dest_denotation (fst (HOLogic.dest_eq (HOLogic.dest_Trueprop concl)))
      val proglen = Hoare_Tactics.program_length lhsprog
      val n' = Thm.cterm_of ctx (Hoare_Tactics.mk_suc_nat (proglen - n))
      val insert_split_n = Ctr_Sugar_Util.cterm_instantiate_pos [SOME n'] @{thm insert_split}
  in
    rtac insert_split_n i  
    THEN Raw_Simplifier.rewrite_goal_tac ctx @{thms split_program_simps} i
  end)

*}

ML {*
fun extract_range_tac _   ([],_)   = error "empty range given"
  | extract_range_tac ctx ([a],len) =
      split_with_seq_tac ctx (a-1)
      THEN' rtac @{thm denotation_eq_seq_snd}
      THEN' split_with_seq_tac ctx len
      THEN' rtac @{thm denotation_eq_seq_fst}
  | extract_range_tac _   (_::_::_,_) = error "extract_range_tac: extracting nested ranges not supported"
*}

thm seq_swap

ML {*
fun swap_tac ctx range len1 (*(A,B,R)*) =
  extract_range_tac ctx range
  THEN' split_with_seq_tac ctx len1
  THEN' rtac @{thm seq_swap2} (*(Drule.instantiate' [] [R,NONE,NONE,A,B] @{thm seq_swap})*)
*}


lemma
(*  assumes "program_footprint {} c3"
  assumes "program_footprint {} c4"
  assumes "program_footprint {} c5" *)
  assumes "LOCAL c3 c4 c5 (x::int variable). hoare {P &m} \<guillemotleft>c1\<guillemotright>; \<guillemotleft>c2\<guillemotright>; c4:=(1::int); c5:=x; c3:=x; \<guillemotleft>c6\<guillemotright> {Q &m}"
  shows   "LOCAL c3 c4 c5 (x::int variable). hoare {P &m} \<guillemotleft>c1\<guillemotright>; \<guillemotleft>c2\<guillemotright>; c3:=x; c4:=(1::int); c5:=x; \<guillemotleft>c6\<guillemotright> {Q &m}"
apply (rule denotation_eq_rule)
apply (tactic \<open>swap_tac @{context} ([3],3) 1 (*(NONE,NONE,NONE)*) 1\<close>)
close simp
close simp
apply simp
by (fact assms)











ML {*
type module = {
  name : string list
}

fun module_name ({name=name, ...} : module) = String.concatWith "." (rev name)
*}


ML {*
structure ModuleData = Generic_Data
  (type T = module list
   val empty = []
   val extend = I
   fun merge (_,_) = error ("ModuleData.merge"))
*}
                                             
ML {*

fun begin_module1 (name:string) lthy : local_theory =
  let val _ = @{print} name
      val _ = @{print} lthy
      val module_stack = ModuleData.get (Context.Proof lthy)
      val full_name = case module_stack of [] => [name] | {name=n,...}::_ => name::n
      val new_module = {name=full_name}
      val lthy = ModuleData.map (fn d => new_module::d) (Context.Proof lthy) |> Context.proof_of
  in
  lthy
  end

fun begin_module (name:string) =
  let fun begin stack = 
        let val full_name = case stack of [] => [name] | {name=n,...}::_ => name::n
            val new_module = {name=full_name}
        in new_module::stack end
  in
  Local_Theory.declaration {pervasive=true, syntax=false}
  (fn _ => ModuleData.map begin)
  end

fun end_module lthy =
  let val stack = ModuleData.get (Context.Proof lthy)
      val _ = if null stack then error "No matching module command" else ()
      val _ = writeln ("Closing module "^module_name (hd stack))
  in
  Local_Theory.declaration {pervasive=true, syntax=false} (fn _ => ModuleData.map tl) lthy
  end

val _ =
  Outer_Syntax.command @{command_keyword module} "Defines a new module"
    (Parse.name --| Parse.begin
      >> (fn name => Toplevel.local_theory NONE NONE (begin_module name)))
val _ =
  Outer_Syntax.command @{command_keyword end_module} "Finished a module definition"
    (Scan.succeed (Toplevel.local_theory NONE NONE end_module))
*}

ML {*
fun current_module ctx = 
  case ModuleData.get (Context.Proof ctx) of [] => NONE
                           | m::_ => SOME m
fun current_module_name ctx =
  case current_module ctx of NONE => [] | SOME m => #name m

fun qualify_in_module ctx bind =
  fold (Binding.qualify true) (current_module_name ctx) bind
*}

module hello begin
module hey begin

ML {* qualify_in_module @{context} @{binding beep} *}

local_setup {* fn lthy => 
  let val (_,lthy) = Local_Theory.define ((qualify_in_module lthy @{binding bla},NoSyn),((@{binding bla_def},[]),@{term "1::int"})) lthy
  in
  lthy
  end
*}

thm bla_def

ML {* ModuleData.get (Context.Proof @{context}) |> hd |> module_name *}

end_module
end_module


thm bla_def

module_type MT =
  proc1 :: "(unit,unit) procedure"

end
