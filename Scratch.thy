theory Scratch
imports Procs_Typed Rewrite Hoare_Typed Hoare_Tactics Lang_Simplifier
keywords "module" :: thy_decl
     and "end_module" :: thy_decl
begin


(* definition "restrict_memory X m = memory_combine X m default" *)





lemma readonly_hoare_untyped:
  shows "program_untyped_readonly X c = (\<forall>a. hoare_untyped (\<lambda>m. \<forall>x\<in>X. memory_lookup_untyped m x = a x) c (\<lambda>m. \<forall>x\<in>X. memory_lookup_untyped m x = a x))"
unfolding program_untyped_readonly_def hoare_untyped_hoare_denotation hoare_denotation_def denotation_readonly_def memory_lookup_untyped_def
by metis

lemma readonly_hoare:
  shows "program_readonly X c = (\<forall>a. hoare {\<forall>x\<in>X. memory_lookup_untyped &m x = a x} \<guillemotleft>c\<guillemotright> {\<forall>x\<in>X. memory_lookup_untyped &m x = a x})"
using denotation_def hoare_untyped program_readonly_def program_untyped_readonly_def readonly_hoare_untyped by auto






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
          by (simp add: A'RB' mm1A'R)
      with `m1\<noteq>?mix` show "?thesis m1" by simp
    qed
    show "Rep_distr (denotation_untyped (Seq b a) m) m2 = bb m ?mix * aa ?mix m2" 
      unfolding seq_distr apply (subst m2_single) apply (subst aux)
      apply (subst nn_integral_singleton_indicator_countspace)
      using aa_pos bb_pos by auto
  qed

  have aux: "\<And>X m m'. (memory_combine X default m = memory_combine X default m') = (\<forall>x\<in>-X. Rep_memory m x = Rep_memory m' x)"
    apply (subst Rep_memory_inject[symmetric]) apply auto by metis 

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
      show ?thesis
        unfolding program_untyped_readonly_def denotation_readonly_def
      proof (rule+)
        fix m m' y
        def den == "denotation_untyped (CallProc x (Proc body pargs ret) a) m"
        assume m': "m' \<in> support_distr (denotation_untyped (CallProc x p a) m)"
        (* hence m': "Rep_distr den m' \<noteq> 0" by (simp add: den_def Proc support_distr_def) *)
        assume "y \<in> R"
        hence y_nin: "y \<notin> set (pu_vars x)" 
          using CallProc.prems by auto
        (* have cases: "\<And>P. \<lbrakk> \<not> vu_global y \<Longrightarrow> P; True \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" by auto *)
        obtain r a' b where den2: "den == apply_to_distr (\<lambda>m'\<Colon>memory. memory_update_untyped_pattern (restore_locals m m') x (r m')) b"
                    and b: "b = denotation_untyped body (memory_update_untyped_pattern (init_locals m) pargs a')"
          unfolding den_def by auto
        then obtain m'' where m''1: "m'' \<in> support_distr b" and m''2: "m' = memory_update_untyped_pattern (restore_locals m m'') x (r m'')"
          using Proc den_def m' by auto
        show "Rep_memory m y = Rep_memory m' y"                               
        proof (cases "vu_global y")
          assume local: "\<not> vu_global y"
          with y_nin have "Rep_memory m' y = Rep_memory (restore_locals m m'') y"
            by (metis m''2 memory_lookup_untyped_def memory_lookup_update_pattern_notsame)
          thus "Rep_memory m y = Rep_memory m' y"
            by (simp add: Rep_restore_locals local)
        next
          assume global: "vu_global y" 
          def m_init == "init_locals m"
          def m_args == "memory_update_untyped_pattern m_init pargs a'"
          have y_nin2: "y \<notin> set (pu_vars pargs)"
            using `y \<in> R` CallProc.prems global unfolding Proc by auto
          have "Rep_memory m y = Rep_memory m_init y"
            by (simp add: Rep_init_locals global m_init_def)
          also have "\<dots> = Rep_memory m_args y"
            using m_args_def memory_lookup_untyped_def memory_lookup_update_pattern_notsame y_nin2 by auto
          also have b: "b = denotation_untyped body m_args"
            using b m_args_def m_init_def by auto
          have yR: "y \<in> (R\<inter>Collect vu_global)" using global `y\<in>R` by auto
          have "(set (pu_vars pargs) \<inter> Collect vu_global \<union> set (write_vars_untyped body) \<inter> Collect vu_global) \<inter> R = {}"
            using CallProc.prems unfolding Proc by auto
          hence "program_untyped_readonly (R\<inter>Collect vu_global) body"
            using CallProc.hyps unfolding Proc by simp
          with b m''1 yR have "Rep_memory m'' y = Rep_memory m_args y"
            by (simp add: denotation_readonly_def program_untyped_readonly_def)
          also have "Rep_memory m'' y = Rep_memory m' y"
            using Rep_restore_locals global m''2 memory_lookup_untyped_def memory_lookup_update_pattern_notsame y_nin by auto
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
  qed
  thus ?thesis by simp
qed


lemma program_readonly_write_vars: "program_readonly (- set(write_vars p)) p"
  using program_untyped_readonly_write_vars[of "Rep_program p"]
  unfolding program_readonly_def program_untyped_readonly_def write_vars_def denotation_def 
  by assumption

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
  THEN rtac @{thm seq_swap2} i
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
