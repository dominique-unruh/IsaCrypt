theory Scratch
imports Procs_Typed Rewrite Hoare_Typed Hoare_Tactics Lang_Simplifier
(* keywords "module" :: thy_decl
     and "end_module" :: thy_decl *)
begin


(* definition "restrict_memory X m = memory_combine X m default" *)





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
    by (simp add: aa_def) 
  have bb_pos: "\<And>x y. bb x y \<ge> 0"
    by (simp add: bb_def) 
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
      by (simp add: Rep_compose_distr aa_def bb_def) 
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
      by (simp add: Rep_compose_distr aa_def bb_def) 
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


                     

lemma program_readonly_write_vars: "program_readonly (- set(write_vars p)) p"
  using program_untyped_readonly_write_vars[of "Rep_program p"]
  unfolding program_readonly_def program_untyped_readonly_def write_vars_def denotation_def 
  by assumption

(* lemma denotation_footprint_def2: "denotation_footprint X d = ((\<forall>m m' z. 
  (\<forall>x\<in>-X. Rep_memory m x = Rep_memory m' x) \<longrightarrow> Rep_distr (d m) m' = Rep_distr (d (memory_combine X m z)) (memory_combine X m' z))
  \<and> (\<forall>m m' z. 
  ~ (\<forall>x\<in>-X. Rep_memory m x = Rep_memory m' x) \<longrightarrow> Rep_distr (d m) m' = 0))"
  unfolding denotation_footprint_def apply auto *)

lemma program_untyped_footprint_vars: "program_untyped_footprint (set(vars_untyped p)) p"
proof -
  fix q
  have "\<And>R. set (vars_untyped p) \<subseteq> R \<Longrightarrow> program_untyped_footprint R p"
    and "\<And>R. set (vars_proc_untyped q) \<subseteq> R \<Longrightarrow> True" 
  proof (induct p and q)
  case Assign thus ?case by auto
  next case Sample thus ?case by auto
  next case Skip 
    have aux: "\<And>f g x. f = g \<Longrightarrow> f x = g x" by simp
    have "\<And>m m'. Rep_memory (memory_combine R default m) = Rep_memory (memory_combine R default m') \<Longrightarrow>
       Rep_memory m' \<noteq> Rep_memory m \<Longrightarrow> (\<And>z. Rep_memory (memory_combine R m' z) \<noteq> Rep_memory (memory_combine R m z))"
    proof -
      fix m m' z
      assume "Rep_memory m' \<noteq> Rep_memory m" then obtain x where x: "Rep_memory m' x \<noteq> Rep_memory m x" by auto
      assume "Rep_memory (memory_combine R default m) = Rep_memory (memory_combine R default m')"
      with x have "x \<in> R" apply (cases "x\<in>R") apply auto apply (drule_tac aux[where x=x]) by auto
      with x show "Rep_memory (memory_combine R m' z) \<noteq> Rep_memory (memory_combine R m z)" 
        apply auto apply (drule_tac aux[where x=x]) by auto
    qed
    thus ?case
      unfolding program_untyped_footprint_def denotation_footprint_def apply simp
      apply (subst Rep_memory_inject[symmetric])+ by simp
  next case While thus ?case by auto
  next case IfTE thus ?case by auto
  next case Seq thus ?case by auto
  next case CallProc thus ?case by auto
  next case Proc thus ?case by auto
  next case ProcAppl thus ?case by auto
  next case ProcPair thus ?case by auto
  next case ProcRef thus ?case by auto
  next case ProcAbs thus ?case by auto
  next case ProcUnpair thus ?case by auto
  qed
  thus ?thesis by auto
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










end
