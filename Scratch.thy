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

definition "program_untyped_footprint X c = denotation_footprint X (denotation_untyped c)"
definition "program_footprint X c = denotation_footprint X (denotation c)"

definition "denotation_readonly X d = (\<forall>m. \<forall>m'\<in>support_distr (d m). \<forall>x\<in>X. Rep_memory m x = Rep_memory m' x)"
definition "program_readonly X c = denotation_readonly X (denotation c)"
definition "program_untyped_readonly X c = denotation_readonly X (denotation_untyped c)"

lemma denotation_footprint_readonly:
  assumes "R\<inter>X={}"
  assumes "denotation_footprint X d"
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


(* TODO move to Distr *)
lemma nn_integral_singleton_indicator:
  assumes "f y \<ge> 0"
  assumes "{y} \<in> sets \<mu>"
  shows "(\<integral>\<^sup>+x. f x * indicator {y} x \<partial>\<mu>) = f y * emeasure \<mu> {y}"
proof -
  have "(\<integral>\<^sup>+x. f x * indicator {y} x \<partial>\<mu>) = (\<integral>\<^sup>+x. f y * indicator {y} x \<partial>\<mu>)"
    by (metis ereal_zero_times indicator_simps(2) singletonD)
  also have "... = f y * emeasure \<mu> {y}"
    apply (rule nn_integral_cmult_indicator)  
    using assms by auto
  finally show ?thesis .
qed

lemma nn_integral_singleton_indicator_countspace:
  assumes "f y \<ge> 0" and "y \<in> M"
  shows "(\<integral>\<^sup>+x. f x * indicator {y} x \<partial>count_space M) = f y"
apply (subst nn_integral_singleton_indicator)
  using assms apply auto
  by (metis mult.comm_neutral one_ereal_def)


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
  def B' == "UNIV-A"

  have "program_untyped_readonly B' a"
    apply (rule program_untyped_footprint_readonly)
    defer close (fact foot_a)
    unfolding B'_def by (simp add: inf_sup_aci(1))
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
          by (metis A'_def B'_def DiffI UNIV_I UnI1 UnI2 mm1B'R)
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

  moreover
  have "\<And>m2. aa m (memory_combine A' m2 m) * bb (memory_combine A' m2 m) m2
            = aa (memory_combine B' m2 m) m2 * bb m (memory_combine B' m2 m)"
      by later

  ultimately have "\<And>m2. Rep_distr (denotation_untyped (Seq a b) m) m2 = Rep_distr (denotation_untyped (Seq b a) m) m2"
    by simp
  thus ?thesis
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

lemma program_footprint_seq:
  assumes "program_footprint A a"
  assumes "program_footprint B b"
  assumes "X \<supseteq> A" and "X \<supseteq> B"
  shows "program_footprint X (seq a b)"
SORRY

lemma
  assumes "program_footprint {} c3"
  assumes "program_footprint {} c4"
  assumes "program_footprint {} c5"
  assumes "hoare {P &m} \<guillemotleft>c1\<guillemotright>; \<guillemotleft>c2\<guillemotright>; \<guillemotleft>c4\<guillemotright>; \<guillemotleft>c5\<guillemotright>; \<guillemotleft>c3\<guillemotright>; \<guillemotleft>c6\<guillemotright> {Q &m}"
  shows  "hoare {P &m} \<guillemotleft>c1\<guillemotright>; \<guillemotleft>c2\<guillemotright>; \<guillemotleft>c3\<guillemotright>; \<guillemotleft>c4\<guillemotright>; \<guillemotleft>c5\<guillemotright>; \<guillemotleft>c6\<guillemotright> {Q &m}"
apply (rule denotation_eq_rule)
 (* Select 3-5  *)
 apply (tactic \<open>split_with_seq_tac @{context} 2 1\<close>)
 apply (rule denotation_eq_seq_snd)
 apply (tactic \<open>split_with_seq_tac @{context} 3 1\<close>)
 apply (rule denotation_eq_seq_fst)
 (* Split 3 / 4-5 *)
 apply (tactic \<open>split_with_seq_tac @{context} 1 1\<close>)
 apply (rule seq_swap[where R=UNIV])
     close (simp add: assms program_footprint_readonly)
    apply (rule program_footprint_readonly)
     close simp
    apply (rule program_footprint_seq)
       close (fact assms) close (fact assms)
     close simp close simp
   close (fact assms) 
  apply (rule program_footprint_seq)
     close (fact assms) close (fact assms)
   close simp close simp close simp
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
