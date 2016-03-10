theory Scratch4
imports Main Hoare_Tactics Procs_Typed RHL_Typed
begin






fun list_pattern_untyped :: "variable_untyped list \<Rightarrow> pattern_untyped" where
  "list_pattern_untyped [] = pattern_ignore unit_type"
| "list_pattern_untyped (x#xs) = pair_pattern_untyped (pattern_1var x) (list_pattern_untyped xs)"


definition "memory_pattern_related p1 p2 m1 m2 = (\<exists>v. m1 = memory_update_pattern m1 p1 v \<and> m2 = memory_update_pattern m2 p2 v)"

lemma memory_pattern_related_variable_pattern [simp]: 
  "memory_pattern_related (variable_pattern x) (variable_pattern y) m1 m2 = (memory_lookup m1 x = memory_lookup m2 y)"
  unfolding memory_pattern_related_def memory_update_variable_pattern
  by (metis memory_update_lookup memory_lookup_update_same)

definition "kill_vars_pattern_untyped p X = Abs_pattern_untyped
  \<lparr> pur_var_getters = filter (\<lambda>(v,g). v \<notin> X) (pu_var_getters p),
    pur_type = pu_type p \<rparr>"
lemma Rep_kill_vars_pattern_untyped: "Rep_pattern_untyped (kill_vars_pattern_untyped p X) =
  \<lparr> pur_var_getters = filter (\<lambda>(v,g). v \<notin> X) (pu_var_getters p),
    pur_type = pu_type p \<rparr>"
      unfolding kill_vars_pattern_untyped_def apply (rule Abs_pattern_untyped_inverse)
      apply auto
      using Rep_pattern_untyped pu_var_getters_def close force
      using Rep_pattern_untyped unfolding pu_var_getters_def split_def
      using pu_type_def by fastforce 
lemma pu_type_kill_vars_pattern_untyped [simp]: "pu_type (kill_vars_pattern_untyped p X) = pu_type p"
  unfolding pu_type_def Rep_kill_vars_pattern_untyped by simp
lemma pu_var_getters_kill_vars_pattern_untyped: "pu_var_getters (kill_vars_pattern_untyped p X) = filter (\<lambda>(v,g). v \<notin> X) (pu_var_getters p)"
  unfolding pu_var_getters_def Rep_kill_vars_pattern_untyped by simp
lemma pu_vars_kill_vars_pattern_untyped: "pu_vars (kill_vars_pattern_untyped p X) = filter (\<lambda>v. v \<notin> X) (pu_vars p)"
  unfolding pu_vars_def pu_var_getters_kill_vars_pattern_untyped split_def filter_map o_def by simp

definition kill_vars_pattern :: "'a::prog_type pattern \<Rightarrow> variable_untyped set \<Rightarrow> 'a pattern" where
  "kill_vars_pattern p X = Abs_pattern (kill_vars_pattern_untyped (Rep_pattern p) X)"
lemma Rep_kill_vars_pattern: "Rep_pattern (kill_vars_pattern p X) = kill_vars_pattern_untyped (Rep_pattern p) X"
  unfolding kill_vars_pattern_def apply (subst Abs_pattern_inverse) by auto
lemma p_var_getters_kill_vars_pattern: "p_var_getters (kill_vars_pattern p X) = filter (\<lambda>(v,g). v \<notin> X) (p_var_getters p)"
  unfolding p_var_getters_def Rep_kill_vars_pattern pu_var_getters_kill_vars_pattern_untyped by simp
lemma p_vars_kill_vars_pattern: "p_vars (kill_vars_pattern p X) = filter (\<lambda>v. v \<notin> X) (p_vars p)"
  unfolding p_vars_def Rep_kill_vars_pattern pu_vars_kill_vars_pattern_untyped by simp


lemma memory_lookup_inject: "memory_lookup_untyped m = memory_lookup_untyped m' \<Longrightarrow> m=m'"
  apply (cases m, cases m', simp)
  apply (subst (asm) Abs_memory_inverse) close simp
  apply (subst (asm) Abs_memory_inverse) close simp
  by simp

lemma memory_update_pattern_getter_kill_vars_pattern_untyped:
  assumes "x \<notin> X"
  shows "memory_update_untyped_pattern_getter (kill_vars_pattern_untyped p X) x = memory_update_untyped_pattern_getter p x"
proof -
  def rg == "rev (pu_var_getters p)"
  have t: "find (\<lambda>p. x = fst p) [p\<leftarrow>rg . fst p \<notin> X] = find (\<lambda>p. x = fst p) rg"
    apply (induction rg) close
    using `x\<notin>X` by auto
  show ?thesis
    unfolding memory_update_untyped_pattern_getter_def pu_var_getters_kill_vars_pattern_untyped 
          split_def rev_filter rg_def[symmetric]
    using t by simp
qed

lemma memory_update_pattern_twice_kill_untyped: 
  "memory_update_untyped_pattern (memory_update_untyped_pattern m p x) q y = 
   memory_update_untyped_pattern (memory_update_untyped_pattern m (kill_vars_pattern_untyped p (set (pu_vars q))) x) q y"
proof (rule memory_lookup_inject[OF ext], case_tac "v \<in> set (pu_vars q)")
  fix v
  assume v: "v \<in> set (pu_vars q)"
  show "memory_lookup_untyped (memory_update_untyped_pattern (memory_update_untyped_pattern m p x) q y) v =
         memory_lookup_untyped
          (memory_update_untyped_pattern (memory_update_untyped_pattern m (kill_vars_pattern_untyped p (set (pu_vars q))) x) q y) v"
    apply (subst lookup_memory_update_untyped_pattern_getter) using v close
    apply (subst lookup_memory_update_untyped_pattern_getter) using v close
    by simp    
next
  fix v
  assume vq: "v \<notin> set (pu_vars q)"
  have eqp: "memory_lookup_untyped (memory_update_untyped_pattern m p x) v =
             memory_lookup_untyped (memory_update_untyped_pattern m (kill_vars_pattern_untyped p (set (pu_vars q))) x) v"
  proof (cases "v\<in>set(pu_vars p)")
  case True
    hence vkill: "v \<in> set (pu_vars (kill_vars_pattern_untyped p (set (pu_vars q))))"
      unfolding pu_vars_kill_vars_pattern_untyped using vq by simp
    show ?thesis 
      apply (subst lookup_memory_update_untyped_pattern_getter) using True close
      apply (subst lookup_memory_update_untyped_pattern_getter) using vkill close
      apply (subst memory_update_pattern_getter_kill_vars_pattern_untyped) using vq close
      by simp
  next case False
    hence vkill: "v \<notin> set (pu_vars (kill_vars_pattern_untyped p (set (pu_vars q))))"
      unfolding pu_vars_kill_vars_pattern_untyped by simp
    show ?thesis 
      apply (subst memory_lookup_update_pattern_notsame) using False close
      apply (subst memory_lookup_update_pattern_notsame) using vkill close
      by simp
  qed
  show "memory_lookup_untyped (memory_update_untyped_pattern (memory_update_untyped_pattern m p x) q y) v =
         memory_lookup_untyped
          (memory_update_untyped_pattern (memory_update_untyped_pattern m (kill_vars_pattern_untyped p (set (pu_vars q))) x) q y) v"
    apply (subst memory_lookup_update_pattern_notsame[where p=q]) using vq close
    apply (subst memory_lookup_update_pattern_notsame[where p=q]) using vq close
    using eqp by simp
qed

lemma memory_update_pattern_twice_kill: 
  "memory_update_pattern (memory_update_pattern m p x) q y = 
   memory_update_pattern (memory_update_pattern m (kill_vars_pattern p (set (p_vars q))) x) q y"
by (metis (no_types, lifting) Rep_kill_vars_pattern memory_update_pattern_def memory_update_pattern_twice_kill_untyped p_vars_def)

lemma no_vars_ignore_pattern_untyped: "pu_vars p = [] \<Longrightarrow> p = pattern_ignore (pu_type p)"
proof -
  assume "pu_vars p = []"
  hence "pu_var_getters p = []"
    unfolding pu_vars_def pu_var_getters_def by auto
  moreover have "pu_type p = pu_type (pattern_ignore (pu_type p))"
    by simp
  ultimately show ?thesis
    by (metis (full_types) Rep_pattern_untyped_inverse old.unit.exhaust pattern_ignore_def pattern_rep.surjective pu_type_def pu_var_getters_def) 
qed

lemma Rep_ignore_pattern': "Rep_pattern (ignore_pattern :: 'a pattern) = pattern_ignore (Type TYPE('a::prog_type))"
  by (simp add: Abs_pattern_inverse ignore_pattern_def)

lemma no_vars_ignore_pattern: "p_vars p = [] \<Longrightarrow> p = ignore_pattern"
proof -
  def p' == "Rep_pattern p"
  assume "p_vars p = []"
  hence "pu_vars p' = []"
    by (simp add: p'_def p_vars_def) 
  hence "p' = pattern_ignore (pu_type p')"
    by (rule no_vars_ignore_pattern_untyped)
  hence "p' = pattern_ignore (Type TYPE('a))"
    by (simp add: p'_def)
  thus "p = ignore_pattern"
    by (metis Rep_pattern_inverse ignore_pattern_def p'_def)
qed

lemma memory_update_pattern_twice [simp]: "memory_update_pattern (memory_update_pattern m p x) p y = memory_update_pattern m p y"
proof -
  def kp == "kill_vars_pattern p (set (p_vars p))"
  have "set (p_vars kp) = {}"
    unfolding kp_def p_vars_kill_vars_pattern by auto
  hence "p_vars kp = []" by auto
  hence ignore: "kp = ignore_pattern"
    by (rule no_vars_ignore_pattern)
  show ?thesis
    apply (subst memory_update_pattern_twice_kill)
    unfolding kp_def[symmetric] ignore by auto
qed


lemma memory_pattern_relatedI: "m1 = memory_update_pattern m1' p1 v \<Longrightarrow> m2 = memory_update_pattern m2' p2 v \<Longrightarrow> memory_pattern_related p1 p2 m1 m2"
  unfolding memory_pattern_related_def apply (rule exI[of _ v]) by auto

lemma pu_vars_list_pattern_untyped [simp]: "pu_vars (list_pattern_untyped xs) = xs"
  apply (induction xs) by auto


lemma rtrans3_rule:
  assumes p:"\<And>m1 m2. P m1 m2 \<Longrightarrow> \<exists>m m'. P1 m1 m \<and> P2 m m' \<and> P3 m' m2"
      and q:"\<And>m1 m2 m m'. Q1 m1 m \<Longrightarrow> Q2 m m' \<Longrightarrow> Q3 m' m2 \<Longrightarrow> Q m1 m2"
      and rhl1: "hoare {P1 &1 &2} \<guillemotleft>c1\<guillemotright> ~ \<guillemotleft>c2\<guillemotright> {Q1 &1 &2}"
      and rhl2: "hoare {P2 &1 &2} \<guillemotleft>c2\<guillemotright> ~ \<guillemotleft>c3\<guillemotright> {Q2 &1 &2}"
      and rhl3: "hoare {P3 &1 &2} \<guillemotleft>c3\<guillemotright> ~ \<guillemotleft>c4\<guillemotright> {Q3 &1 &2}"
  shows "hoare {P &1 &2} \<guillemotleft>c1\<guillemotright> ~ \<guillemotleft>c4\<guillemotright> {Q &1 &2}"
proof -
  def Q12 == "\<lambda>m1 m'. \<exists>m. Q1 m1 m \<and> Q2 m m'"
  def P12 == "\<lambda>m1 m'. \<exists>m. P1 m1 m \<and> P2 m m'"
  have rhl12: "rhoare P12 c1 c3 Q12"
    apply (rule rtrans_rule[OF _ _ rhl1 rhl2])
    unfolding P12_def Q12_def by auto
  show ?thesis
    apply (rule rtrans_rule[OF _ _ rhl12 rhl3])
    unfolding P12_def Q12_def
     using p close metis
    using q by metis
qed

lemma list_pattern_untyped_list_expression_untyped: "memory_update_untyped_pattern m (list_pattern_untyped xs) (eu_fun (list_expression_untyped xs) m) = m"
proof (induction xs arbitrary: m)
case Nil show ?case by auto
next case (Cons x xs')
  have type: "pu_type (list_pattern_untyped xs) = eu_type (list_expression_untyped xs)" for xs
  proof (induction xs)
  case Nil show ?case apply simp apply (subst eu_type_const_expression_untyped) apply (metis Type_def embedding_Type unit_type_def) by simp
  next case Cons thus ?case by auto
  qed
  have u1: "memory_update_untyped_pattern m (pattern_1var x) (eu_fun (var_expression_untyped x) m) = m"
    by simp
  have u2: "memory_update_untyped_pattern (memory_update_untyped_pattern m (pattern_1var x) (eu_fun (var_expression_untyped x) m))
     (list_pattern_untyped xs') (eu_fun (list_expression_untyped xs') m) = m"
    apply (subst u1) by (fact Cons)

  show ?case
    apply (simp add: eu_fun_pair_expression_untyped)
    apply (subst memory_update_pair_pattern_untyped)
      close (auto simp: Rep_var_expression_untyped eu_fun_def)
     using type close simp
    using u2 by simp
qed


lemma assertion_footprint_left_UNIV: 
  shows "assertion_footprint_left UNIV P"
    unfolding assertion_footprint_left_def
    using memory_lookup_inject[OF ext] by auto

lemma assertion_footprint_right_UNIV: 
  shows "assertion_footprint_right UNIV P"
    unfolding assertion_footprint_right_def
    using memory_lookup_inject[OF ext] by auto

lemma assertion_footprint_left_update:
  assumes "Y \<subseteq> insert (mk_variable_untyped x) X"
  assumes "assertion_footprint_left Y P"
  shows "assertion_footprint_left X (\<lambda>m m'. P (memory_update m x v) m')"
unfolding memory_update_def
apply (rule assertion_footprint_left_update_untyped)
using assms by auto

lemma assertion_footprint_right_update:
  assumes "Y \<subseteq> insert (mk_variable_untyped x) X"
  assumes "assertion_footprint_right Y P"
  shows "assertion_footprint_right X (\<lambda>m m'. P m (memory_update m' x v))"
unfolding memory_update_def
apply (rule assertion_footprint_right_update_untyped)
using assms by auto


lemma callproc_equiv: 
  assumes globals_V1: "set (vars_proc_global f) \<subseteq> V1"
  assumes V2V1: "V2 \<subseteq> V1"
  assumes x1V2: "set (p_vars x1) \<inter> V2 = {}"
  assumes x2V2: "set (p_vars x2) \<inter> V2 = {}"
  shows "rhoare (\<lambda>m1 m2. (\<forall>v\<in>V1. memory_lookup_untyped m1 v = memory_lookup_untyped m2 v)
                      \<and> e_fun e1 m1 = e_fun e2 m2)
                   (callproc x1 f e1) (callproc x2 f e2)
                (\<lambda>m1 m2. (\<forall>v\<in>V2. memory_lookup_untyped m1 v = memory_lookup_untyped m2 v)
                      \<and> memory_pattern_related x1 x2 m1 m2)"
proof (rule rhoareI, goal_cases)
case (1 m1 m2)  
  hence eq_m1_m2: "memory_lookup_untyped m1 v = memory_lookup_untyped m2 v"
        if "v\<in>V1" for v 
    using that by auto
  from 1 have e1e2: "e_fun e1 m1 = e_fun e2 m2" by simp
  def argval == "e_fun e1 m1"
  def m1a == "init_locals m1"
  def m1b == "memory_update_pattern m1a (p_arg f) argval"
  def m2a == "init_locals m2"
  def m2b == "memory_update_pattern m2a (p_arg f) argval"

  have eq_m12a: "memory_lookup_untyped m1a v = memory_lookup_untyped m2a v" if "v\<in>V1" for v 
    using that eq_m1_m2 by (simp add: Rep_init_locals m1a_def m2a_def)
  have eq_m12a_loc: "memory_lookup_untyped m1a v = memory_lookup_untyped m2a v" if "\<not> vu_global v" for v 
    using that by (simp add: Rep_init_locals m1a_def m2a_def)
  have eq_m12b_V1: "memory_lookup_untyped m1b v = memory_lookup_untyped m2b v" if "v\<in>V1" for v 
    unfolding m1b_def m2b_def memory_update_pattern_def using that eq_m12a
    by (metis lookup_memory_update_untyped_pattern_getter memory_lookup_update_pattern_notsame)
  have eq_m12b_loc: "memory_lookup_untyped m1b v = memory_lookup_untyped m2b v" if "\<not> vu_global v" for v 
    unfolding m1b_def m2b_def memory_update_pattern_def using eq_m12a_loc that
    by (metis lookup_memory_update_untyped_pattern_getter memory_lookup_update_pattern_notsame)
(*   have "memory_lookup_untyped m1b v = memory_lookup_untyped m2b v" if "v \<in> set(p_vars(p_arg f))" for v 
    using that by auto *)

  def V1loc == "V1 \<union> {x. \<not> vu_global x}"

  have vars_V1loc: "set(vars(p_body f)) \<subseteq> V1loc"
    using globals_V1 unfolding vars_proc_global_def V1loc_def by auto
  with eq_m12b_V1 eq_m12b_loc
  have eq_m12b: "memory_lookup_untyped m1b v = memory_lookup_untyped m2b v" if "v \<in> V1loc" for v
    using that V1loc_def by auto

  have "obs_eq V1loc V1loc (p_body f) (p_body f)"
    unfolding obs_eq_obs_eq_untyped
    apply (rule self_obseq_vars)
    using vars_V1loc by (simp_all add: vars_def) 
  
  then obtain \<mu> where \<mu>fst: "apply_to_distr fst \<mu> = denotation (p_body f) m1b"
                  and \<mu>snd: "apply_to_distr snd \<mu> = denotation (p_body f) m2b"
                  and \<mu>post: "\<And>m1' m2' x. (m1',m2') \<in> support_distr \<mu> \<Longrightarrow> x\<in>V1loc \<Longrightarrow> 
                                memory_lookup_untyped m1' x = memory_lookup_untyped m2' x"
    unfolding obs_eq_def rhoare_def
    using eq_m12b by blast 

  def finalize == "\<lambda>m x. \<lambda>m'. let res = e_fun (p_return f) m'; m' = restore_locals m m' in memory_update_pattern m' x res"

  def \<mu>' == "apply_to_distr (\<lambda>(m1',m2'). (finalize m1 x1 m1', finalize m2 x2 m2')) \<mu>"

  have "apply_to_distr fst \<mu>' = apply_to_distr (\<lambda>m1'. finalize m1 x1 m1') (apply_to_distr fst \<mu>)"
    unfolding \<mu>'_def by (simp add: split_def)
  also have "\<dots> = apply_to_distr (\<lambda>m1'. finalize m1 x1 m1') (denotation (p_body f) m1b)"
    using \<mu>fst by simp
  also have "\<dots> = denotation (callproc x1 f e1) m1"
    unfolding argval_def m1a_def m1b_def finalize_def
    apply (subst denotation_callproc) by auto
  finally have \<mu>'fst: "apply_to_distr fst \<mu>' = denotation (callproc x1 f e1) m1" by assumption

  have "apply_to_distr snd \<mu>' = apply_to_distr (\<lambda>m2'. finalize m2 x2 m2') (apply_to_distr snd \<mu>)"
    unfolding \<mu>'_def by (simp add: split_def)
  also have "\<dots> = apply_to_distr (\<lambda>m2'. finalize m2 x2 m2') (denotation (p_body f) m2b)"
    using \<mu>snd by simp
  also have "\<dots> = denotation (callproc x2 f e2) m2"
    unfolding argval_def m2a_def m2b_def finalize_def e1e2
    apply (subst denotation_callproc) by auto
  finally have \<mu>'snd: "apply_to_distr snd \<mu>' = denotation (callproc x2 f e2) m2"
    by assumption

  have \<mu>'post: "\<And>x. x\<in>V2 \<Longrightarrow> memory_lookup_untyped m1' x = memory_lookup_untyped m2' x"
   and \<mu>'post2: "memory_pattern_related x1 x2 m1' m2'"
               if supp: "(m1',m2') \<in> support_distr \<mu>'" 
               for m1' m2'
  proof -
    from supp obtain m1'' m2'' where 
        m1': "m1' = finalize m1 x1 m1''" and m2': "m2' = finalize m2 x2 m2''" and "(m1'',m2'') \<in> support_distr \<mu>"
        unfolding \<mu>'_def by auto
    hence eq_m12'': "\<And>x. x\<in>V1loc \<Longrightarrow> memory_lookup_untyped m1'' x = memory_lookup_untyped m2'' x"
      using \<mu>post by simp

    have ret_V1loc: "set (e_vars (p_return f)) \<subseteq> V1loc"
      unfolding V1loc_def using globals_V1 unfolding vars_proc_global_def by auto
    have ret12: "e_fun (p_return f) m1'' = e_fun (p_return f) m2''"
      apply (rule e_fun_footprint)
      apply (rule eq_m12'') 
      using ret_V1loc by auto

    show "memory_pattern_related x1 x2 m1' m2'"
      apply (rule memory_pattern_relatedI)
      unfolding m1' m2' finalize_def ret12 by auto

    show "memory_lookup_untyped m1' x = memory_lookup_untyped m2' x" if "x\<in>V2" for x
    proof -
      def ret == "e_fun (p_return f) m1''"
      def m1l == "restore_locals m1 m1''"
      def m2l == "restore_locals m2 m2''"
      have "m1' = memory_update_pattern m1l x1 ret"
        unfolding ret_def m1' finalize_def m1l_def by auto
      have "m2' = memory_update_pattern m2l x2 ret"
        unfolding ret_def m2' finalize_def m2l_def ret12 by auto

      have xx1: "x \<notin> set (p_vars x1)" and xx2: "x \<notin> set (p_vars x2)"
        using x1V2 x2V2 that by auto

      have "memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
        using V2V1 eq_m1_m2 that by blast
      moreover have "memory_lookup_untyped m1'' x = memory_lookup_untyped m2'' x"
        using V1loc_def V2V1 eq_m12'' that by auto
      ultimately have "memory_lookup_untyped (restore_locals m1 m1'') x = memory_lookup_untyped (restore_locals m2 m2'') x" 
        unfolding Rep_restore_locals by simp

      then have "memory_lookup_untyped (memory_update_pattern (restore_locals m1 m1'') x1 ret) x =
                 memory_lookup_untyped (memory_update_pattern (restore_locals m2 m2'') x2 ret) x"
        unfolding memory_update_pattern_def
        apply (subst memory_lookup_update_pattern_notsame) close (metis p_vars_def xx1)
        apply (subst memory_lookup_update_pattern_notsame) close (metis p_vars_def xx2)
        by assumption
      then show ?thesis
        unfolding m1' m2' finalize_def ret_def[symmetric] ret12[symmetric] by simp
    qed
  qed

  from \<mu>'fst \<mu>'snd \<mu>'post \<mu>'post2 show ?case
    apply (rule_tac exI[of _ \<mu>']) by auto
qed


lemma assertion_footprint_left_update_pattern:
  assumes "Y \<subseteq> X \<union> set (p_vars pat)"
  assumes "assertion_footprint_left Y P"
  shows "assertion_footprint_left X (\<lambda>m m'. P (memory_update_pattern m pat x) m')"
unfolding memory_update_pattern_def
apply (rule assertion_footprint_left_update_pattern_untyped)
using assms unfolding p_vars_def by auto

lemma assertion_footprint_right_update_pattern:
  assumes "Y \<subseteq> X \<union> set (p_vars pat)"
  assumes "assertion_footprint_right Y P"
  shows "assertion_footprint_right X (\<lambda>m m'. P m (memory_update_pattern m' pat x))"
unfolding memory_update_pattern_def
apply (rule assertion_footprint_right_update_pattern_untyped)
using assms unfolding p_vars_def by auto

lemma program_readonly_mono:
  assumes mono: "A \<le> B"
  assumes foot: "program_readonly B d"
  shows "program_readonly A d"
by (meson denotation_readonly_def foot mono program_readonly_def subset_iff)



lemma call_rule:
  fixes globals_f1 globals_f2 and x1::"'x1::prog_type pattern" and x2::"'x2::prog_type pattern" 
    and y1::"'y1::prog_type expression" and y2::"'y2::prog_type expression" 
    and res1::"'x1 variable" and res2::"'x2 variable" and A B P Q 
  assumes globals_f1: "set(write_vars_proc_global f1) \<subseteq> set globals_f1"
  assumes globals_f2: "set(write_vars_proc_global f2) \<subseteq> set globals_f2"
  assumes args1_nin_f1: "mk_variable_untyped args1 \<notin> set (vars_proc_global f1)"
  assumes args2_nin_f2: "mk_variable_untyped args2 \<notin> set (vars_proc_global f2)"
  assumes footQ1: "assertion_footprint_left (-{mk_variable_untyped args1}) Q"
  assumes footQ2: "assertion_footprint_right (-{mk_variable_untyped args2}) Q"
  assumes f1f2: "rhoare P
              (callproc (variable_pattern res1) f1 (var_expression args1))
              (callproc (variable_pattern res2) f2 (var_expression args2))
              Q"
  defines "QB == (\<lambda>m1 m2. (\<forall>gL gR xL xR x'L x'R. 
                     Q (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f1) gL) (list_pattern_untyped (p_vars x1)) x'L) res1 xL)
                       (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f2) gR) (list_pattern_untyped (p_vars x2)) x'R) res2 xR)
                \<longrightarrow> B (memory_update_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f1) gL) x1 xL)
                      (memory_update_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f2) gR) x2 xR)))"
  defines "C == (\<lambda>m1 m2. P (memory_update m1 args1 (e_fun y1 m1)) (memory_update m2 args2 (e_fun y2 m2)) \<and> QB m1 m2)"
  assumes p1p2: "rhoare A p1 p2 C"
  shows "rhoare A (seq p1 (callproc x1 f1 y1)) (seq p2 (callproc x2 f2 y2)) B"
proof -
  def P' == "\<lambda>m1 m2. P (memory_update m1 args1 (e_fun y1 m1)) (memory_update m2 args2 (e_fun y2 m2))"
  def x1l == "list_pattern_untyped (p_vars x1)"
  def x2l == "list_pattern_untyped (p_vars x2)"
  def Q' == "\<lambda>m1 m2. (\<exists>res1_val res2_val x1_val x2_val. 
      memory_update_pattern m1 x1 res1_val = m1 \<and> memory_update_pattern m2 x2 res2_val = m2 \<and>
      Q (memory_update (memory_update_untyped_pattern m1 x1l x1_val) res1 res1_val) (memory_update (memory_update_untyped_pattern m2 x2l x2_val) res2 res2_val))"

  def VV1 == "- {mk_variable_untyped args1}"
  def VV2 == "UNIV - {mk_variable_untyped args1, mk_variable_untyped res1} - set(p_vars x1)"
  def VV1' == "- {mk_variable_untyped args2}"
  def VV2' == "UNIV - {mk_variable_untyped args2, mk_variable_untyped res2} - set(p_vars x2)"

  have y1_VV1: "mk_variable_untyped (args1::'y1 variable) \<notin> VV1" unfolding VV1_def by simp
  have vv1_1: "set (vars_proc_global f1) \<subseteq> VV1" unfolding VV1_def using args1_nin_f1 by auto

  have y2_VV1': "mk_variable_untyped (args2::'y2 variable) \<notin> VV1'" unfolding VV1'_def by simp
  have x1: "set (vars_proc_global f2) \<subseteq> VV1'" unfolding VV1'_def using args2_nin_f2 by auto

  have vv1_2: "VV2 \<subseteq> VV1" unfolding VV2_def VV1_def by auto
  have x1_vv2: "set (p_vars x1) \<inter> VV2 = {}" unfolding VV2_def by auto
  have res_vv2: "set (p_vars (variable_pattern res1 :: 'x1 pattern)) \<inter> VV2 = {}" unfolding VV2_def by auto

  have x2: "VV2' \<subseteq> VV1'" unfolding VV2'_def VV1'_def by auto
  have x3: "set (p_vars (variable_pattern res2 :: 'x2 pattern)) \<inter> VV2' = {}" unfolding VV2'_def by auto
  have x4: "set (p_vars x2) \<inter> VV2' = {}" unfolding VV2'_def by auto

  have foot_Q1: "assertion_footprint_left (insert (mk_variable_untyped (res1::'x1 variable)) VV2 \<union> set(p_vars x1)) Q" 
    apply (rule assertion_footprint_left_mono[OF _ footQ1]) unfolding VV2_def by auto

  have foot_Q2: "assertion_footprint_right (insert (mk_variable_untyped (res2::'x2 variable)) VV2' \<union> set(p_vars x2)) Q"
    apply (rule assertion_footprint_right_mono[OF _ footQ2]) unfolding VV2'_def by auto
  (* have foot_Q1': "assertion_footprint_left (insert (mk_variable_untyped (res1::'x1 variable)) {x. vu_global x}) Q" 
  have foot_Q2': "assertion_footprint_right (insert (mk_variable_untyped (res2::'x2 variable)) {x. vu_global x}) Q" 
  have foot_B1: "assertion_footprint_left {x. vu_global x} B" 
  have foot_B2: "assertion_footprint_right {x. vu_global x} B"  *)


  have x1_f1_res_f1: "hoare {\<lambda>m1 m2. (\<forall>v\<in>VV1. memory_lookup_untyped m1 v = memory_lookup_untyped m2 v) \<and> e_fun y1 m1 = e_fun (var_expression args1) m2}
          \<guillemotleft>callproc x1 f1 y1\<guillemotright> ~ \<guillemotleft>callproc (variable_pattern res1) f1 (var_expression args1)\<guillemotright>
        {\<lambda>m1 m2. (\<forall>v\<in>VV2. memory_lookup_untyped m1 v = memory_lookup_untyped m2 v) \<and> memory_pattern_related x1 (variable_pattern res1) m1 m2}"
    apply (rule callproc_equiv)
    using vv1_1 vv1_2 x1_vv2 res_vv2 by auto

  have res_f2_x2_f2: "hoare {\<lambda>m1 m2. (\<forall>v\<in>VV1'. memory_lookup_untyped m1 v = memory_lookup_untyped m2 v) \<and> e_fun (var_expression args2) m1 = e_fun y2 m2}
        \<guillemotleft>callproc (variable_pattern res2) f2 (var_expression args2)\<guillemotright> ~ \<guillemotleft>callproc x2 f2 y2\<guillemotright> 
          {\<lambda>m1 m2. (\<forall>v\<in>VV2'. memory_lookup_untyped m1 v = memory_lookup_untyped m2 v) \<and> memory_pattern_related (variable_pattern res2) x2 m1 m2}"
    apply (rule callproc_equiv)
    using x1 x2 x3 x4 by auto

  have t3: "\<exists>m m'. ((\<forall>v\<in>VV1. memory_lookup_untyped m1 v = memory_lookup_untyped m v) \<and>
                     e_fun y1 m1 = e_fun (var_expression args1) m) \<and>
                    P m m' \<and>
                    (\<forall>v\<in>VV1'. memory_lookup_untyped m' v = memory_lookup_untyped m2 v) \<and> e_fun (var_expression args2) m' = e_fun y2 m2"
                    if "P' m1 m2" for m1 m2
    apply (rule exI[of _ "memory_update m1 args1 (e_fun y1 m1)"], rule exI[of _ "memory_update m2 args2 (e_fun y2 m2)"])
    using y1_VV1 y2_VV1' that unfolding P'_def by simp

  have t4: "Q' m1 m2"
       if eq2: "\<forall>v\<in>VV2'. memory_lookup_untyped m' v = memory_lookup_untyped m2 v" 
       and res_x2: "memory_pattern_related (variable_pattern res2) x2 m' m2" 
       and eq1: "\<forall>v\<in>VV2. memory_lookup_untyped m1 v = memory_lookup_untyped m v" 
       and x1_res: "memory_pattern_related x1 (variable_pattern res1) m1 m"
       and "Q m m'" for m1 m2 m m'
  proof -
    def res1_val == "memory_lookup m res1 :: 'x1"
    def res2_val == "memory_lookup m' res2 :: 'x2"
    def x1_val == "eu_fun (list_expression_untyped (p_vars x1)) m"
    def x2_val == "eu_fun (list_expression_untyped (p_vars x2)) m'"

    from x1_res
    obtain v where x1_v: "m1 = memory_update_pattern m1 x1 v" and res_v: "m = memory_update_pattern m (variable_pattern res1) v"
      unfolding memory_pattern_related_def by auto
    have "v = res1_val" unfolding res1_val_def apply (subst res_v) by simp
    have x1_res1_val: "memory_update_pattern m1 x1 res1_val = m1" using x1_v `v=res1_val` by simp

    from res_x2
    obtain w where res_w: "m' = memory_update_pattern m' (variable_pattern res2) w" and x2_w: "m2 = memory_update_pattern m2 x2 w"
      unfolding memory_pattern_related_def by auto
    have "w = res2_val" unfolding res2_val_def apply (subst res_w) by simp
    have x2_res2_val: "memory_update_pattern m2 x2 res2_val = m2" using x2_w `w=res2_val` by simp

(*     have x1l: "memory_update_untyped_pattern m1 x1l x1_val = m1"
      unfolding x1l_def x1_val_def x2l_def x2_val_def 
      unfolding list_pattern_untyped_list_expression_untyped by simp *)

    have "Q (memory_update (memory_update_untyped_pattern m1 x1l x1_val) res1 res1_val) (memory_update (memory_update_untyped_pattern m2 x2l x2_val) res2 res2_val) = Q m (memory_update (memory_update_untyped_pattern m2 x2l x2_val) res2 res2_val)"
      apply (rule assertion_footprint_leftE[OF foot_Q1])
      using res1_val_def eq1 apply auto
       close (metis list_pattern_untyped_list_expression_untyped lookup_memory_update_untyped_pattern_getter memory_lookup_update_pattern_notsame x1_val_def x1l_def)
      by (metis list_pattern_untyped_list_expression_untyped lookup_memory_update_untyped_pattern_getter pu_vars_list_pattern_untyped x1_val_def x1l_def) 
    also have "\<dots> = Q m m'"
      apply (rule assertion_footprint_rightE[OF foot_Q2])
      using res2_val_def eq2 apply auto
       close (metis list_pattern_untyped_list_expression_untyped lookup_memory_update_untyped_pattern_getter memory_lookup_update_pattern_notsame x2_val_def x2l_def)
      by (metis list_pattern_untyped_list_expression_untyped lookup_memory_update_untyped_pattern_getter pu_vars_list_pattern_untyped x2_val_def x2l_def) 
  finally have Q': "Q (memory_update (memory_update_untyped_pattern m1 x1l x1_val) res1 res1_val)  
                      (memory_update (memory_update_untyped_pattern m2 x2l x2_val) res2 res2_val)"
    using that by simp                      
      

(*     have "Q (memory_update m1 res1 res1_val) (memory_update m2 res2 res2_val) = Q m (memory_update m2 res2 res2_val)"
      apply (rule assertion_footprint_leftE[OF foot_Q1])
      using res1_val_def eq1 by auto
    also have "\<dots> = Q m m'"
      apply (rule assertion_footprint_rightE[OF foot_Q2])
      using res2_val_def eq2 by auto
    finally have "Q (memory_update m1 res1 res1_val) (memory_update m2 res2 res2_val)"
      using `Q m m'` by simp
    hence Q': "Q (memory_update (memory_update_untyped_pattern m1 x1l x1_val) res1 res1_val)  
                 (memory_update (memory_update_untyped_pattern m2 x2l x2_val) res2 res2_val)"
      unfolding x1l_def x1_val_def x2l_def x2_val_def 
      unfolding list_pattern_untyped_list_expression_untyped by assumption *)

    from Q' x1_res1_val x2_res2_val show ?thesis unfolding Q'_def by auto
  qed

  have rhoareP'Q': "rhoare P' (callproc x1 f1 y1) (callproc x2 f2 y2) Q'"
    apply (rule rtrans3_rule[OF _ _ x1_f1_res_f1 f1f2 res_f2_x2_f2])
     close (rule t3, simp)
    by (rule t4, simp_all)

(*   have foot_QB1: "assertion_footprint_left ({x. vu_global x} - set globals_f1 - set (p_vars x1)) QB"
    unfolding QB_def
    apply (rule assertion_footprint_left_forall)+
    apply (rule assertion_footprint_left_op2[where f="op\<longrightarrow>"])
     apply (rule assertion_footprint_left_update_pattern_untyped[where Y="{x. vu_global x} - set (p_vars x1)"])
      close (simp, blast)
     apply (rule assertion_footprint_left_update_pattern[where Y="{x. vu_global x}"])
      close simp
     apply (rule assertion_footprint_left_update[where Y="insert (mk_variable_untyped res1) {x. vu_global x}"])
      close (simp)
     apply (rule assertion_footprint_left_map_other)
     close (fact foot_Q1')
    apply (rule assertion_footprint_left_update_pattern_untyped[where Y="{x. vu_global x} - set (p_vars x1)"])
      close (simp, blast)
     apply (rule assertion_footprint_left_update_pattern[where Y="{x. vu_global x}"])
      close simp
     apply (rule assertion_footprint_left_map_other)
     by (fact foot_B1)
 *) (*  have foot_QB2: "assertion_footprint_right ({x. vu_global x} - set globals_f2 - set (p_vars x2)) QB"
    unfolding QB_def
    apply (rule assertion_footprint_right_forall)+
    apply (rule assertion_footprint_right_op2[where f="op\<longrightarrow>"])
     apply (rule assertion_footprint_right_update_pattern_untyped[where Y="{x. vu_global x} - set (p_vars x2)"])
      close (simp, blast)
     apply (rule assertion_footprint_right_update_pattern[where Y="{x. vu_global x}"])
      close simp
     apply (rule assertion_footprint_right_update[where Y="insert (mk_variable_untyped res2) {x. vu_global x}"])
      close (simp)
     apply (rule assertion_footprint_right_map_other)
     close (fact foot_Q2')
    apply (rule assertion_footprint_right_update_pattern_untyped[where Y="{x. vu_global x} - set (p_vars x2)"])
      close (simp, blast)
     apply (rule assertion_footprint_right_update_pattern[where Y="{x. vu_global x}"])
      close simp
     apply (rule assertion_footprint_right_map_other)
     by (fact foot_B2) *)

  have foot_QB1: "assertion_footprint_left (UNIV - set globals_f1 - set (p_vars x1)) QB"
    unfolding QB_def
    apply (rule assertion_footprint_left_forall)+
    apply (rule assertion_footprint_left_op2[where f="op\<longrightarrow>"])
     apply (rule assertion_footprint_left_update_pattern_untyped[where Y="UNIV - set (p_vars x1)"])
      close (simp, blast)
     apply (rule assertion_footprint_left_update_pattern_untyped[where Y="UNIV"])
      close simp
     apply (rule assertion_footprint_left_update[where Y="UNIV"])
      close
     close (rule assertion_footprint_left_UNIV)
    apply (rule assertion_footprint_left_update_pattern_untyped[where Y="UNIV - set (p_vars x1)"])
     close (simp, blast)
    apply (rule assertion_footprint_left_update_pattern[where Y="UNIV"])
     close simp
    by (rule assertion_footprint_left_UNIV)
  have foot_QB2: "assertion_footprint_right (UNIV - set globals_f2 - set (p_vars x2)) QB"
    unfolding QB_def
    apply (rule assertion_footprint_right_forall)+
    apply (rule assertion_footprint_right_op2[where f="op\<longrightarrow>"])
     apply (rule assertion_footprint_right_update_pattern_untyped[where Y="UNIV - set (p_vars x2)"])
      close (simp, blast)
     apply (rule assertion_footprint_right_update_pattern_untyped[where Y="UNIV"])
      close simp
     apply (rule assertion_footprint_right_update[where Y="UNIV"])
      close
     close (rule assertion_footprint_right_UNIV)
    apply (rule assertion_footprint_right_update_pattern_untyped[where Y="UNIV - set (p_vars x2)"])
     close (simp, blast)
    apply (rule assertion_footprint_right_update_pattern[where Y="UNIV"])
     close simp
    by (rule assertion_footprint_right_UNIV)
    
(*   have ro_f1: "program_readonly ({x. vu_global x} - set globals_f1 - set (p_vars x1)) (callproc x1 f1 y1)"
    apply (rule program_readonly_mono[rotated])
     close (rule program_readonly_write_vars)
    using globals_f1 by auto
  have ro_f2: "program_readonly ({x. vu_global x} - set globals_f2 - set (p_vars x2)) (callproc x2 f2 y2)"
    apply (rule program_readonly_mono[rotated])
     close (rule program_readonly_write_vars)
    using globals_f2 by auto
 *)
  have ro_f1: "program_readonly (UNIV - set globals_f1 - set (p_vars x1)) (callproc x1 f1 y1)"
    apply (rule program_readonly_mono[rotated])
     close (rule program_readonly_write_vars)
    using globals_f1 by auto
  have ro_f2: "program_readonly (UNIV - set globals_f2 - set (p_vars x2)) (callproc x2 f2 y2)"
    apply (rule program_readonly_mono[rotated])
     close (rule program_readonly_write_vars)
    using globals_f2 by auto

  have rhoareQB: "hoare {P' &1 &2 \<and> QB &1 &2} \<guillemotleft>callproc x1 f1 y1\<guillemotright> ~ \<guillemotleft>callproc x2 f2 y2\<guillemotright> {Q' &1 &2 \<and> QB &1 &2}"
    apply (rule frame_rule)
        close (fact foot_QB1)
       close (fact foot_QB2)
      close (fact ro_f1)
     close (fact ro_f2)
    by (fact rhoareP'Q')

  have QB_Q: "B m1 m2" if Q'm1m2: "Q' m1 m2" and QBm1m2: "QB m1 m2" for m1 m2
  proof -
    from Q'm1m2 obtain res1_val res2_val x1_val x2_val
      where ux1: "memory_update_pattern m1 x1 res1_val = m1"
        and ux2: "memory_update_pattern m2 x2 res2_val = m2"
        and Q: "Q (memory_update (memory_update_untyped_pattern m1 x1l x1_val) res1 res1_val) 
                  (memory_update (memory_update_untyped_pattern m2 x2l x2_val) res2 res2_val)"
      unfolding Q'_def by auto

    def gL == "eu_fun (list_expression_untyped globals_f1) m1"
    def gR == "eu_fun (list_expression_untyped globals_f2) m2"

    have Q2: "Q (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f1) gL) x1l x1_val) res1 res1_val)
                (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f2) gR) x2l x2_val) res2 res2_val)"
      unfolding gL_def apply (subst list_pattern_untyped_list_expression_untyped)
      unfolding gR_def apply (subst list_pattern_untyped_list_expression_untyped)
      unfolding ux1 ux2 by (fact Q)

    from QBm1m2[unfolded QB_def, folded x1l_def x2l_def, rule_format, of gL x1_val res1_val gR x2_val res2_val] 
    have B2: "B (memory_update_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f1) gL) x1 res1_val)
                (memory_update_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f2) gR) x2 res2_val)"
    unfolding QB_def using that Q2 by simp

    show "B m1 m2"
      using B2
      unfolding gL_def apply (subst (asm) list_pattern_untyped_list_expression_untyped)
      unfolding gR_def apply (subst (asm) list_pattern_untyped_list_expression_untyped)
      unfolding ux1 ux2 by simp
  qed

  have rhoareCQ: "hoare {C &1 &2} \<guillemotleft>callproc x1 f1 y1\<guillemotright> ~ \<guillemotleft>callproc x2 f2 y2\<guillemotright> {B &1 &2}"
    apply (rule rconseq_rule[rotated -1])
      close (fact rhoareQB)
     unfolding C_def P'_def close
    using QB_Q by auto

  show ?thesis
    apply (rule rseq_rule)
     close (fact p1p2)
    by (fact rhoareCQ)
qed

(* Proof plan: 

- Show:  rhoare    P{args/y}  (callproc x=f(y))  Q{x/res}    (substitution)   \<longrightarrow>  rhoareP'Q'
- Show:  footprint QB   disjoint of   callproc x=f(y)
- Show:  rhoare    C=P{args/y}\<and>QB     (callproc x=f(y))   Q{res/x}\<and>QB   (frame_rule) \<longrightarrow> rhoareQB
- Show:  Q{res/x} \<and> QB \<Longrightarrow> B
- Show:  rhoare    C     (callproc x=f(y))   B    (conseq)
- Show:  rhoare    A     (p; callproc x=f(y))   B    (seq with assm)

*)
