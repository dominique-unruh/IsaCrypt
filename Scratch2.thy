theory Scratch2
imports Main Hoare_Tactics Procs_Typed RHL_Typed
begin

abbreviation "res == LVariable ''res''"
abbreviation "args == LVariable ''args''"

lemma rhoare_untypedI: 
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow>
            (\<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped p1 m1 \<and>
                  apply_to_distr snd \<mu> = denotation_untyped p2 m2 \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2'))"
  shows "rhoare_untyped P p1 p2 Q"
unfolding rhoare_untyped_rhoare_denotation rhoare_denotation_def using assms by simp

lemma rhoare_untypedE: 
  assumes "rhoare_untyped P p1 p2 Q"
  assumes "P m1 m2"
  shows "\<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped p1 m1 \<and>
                  apply_to_distr snd \<mu> = denotation_untyped p2 m2 \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
using assms unfolding rhoare_untyped_rhoare_denotation rhoare_denotation_def by simp

lemma rhoareI: 
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow>
            (\<exists>\<mu>. apply_to_distr fst \<mu> = denotation p1 m1 \<and>
                  apply_to_distr snd \<mu> = denotation p2 m2 \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2'))"
  shows "rhoare P p1 p2 Q"
unfolding rhoare_def using assms by simp

lemma rhoareE: 
  assumes "rhoare P p1 p2 Q"
  assumes "P m1 m2"
  shows "\<exists>\<mu>. apply_to_distr fst \<mu> = denotation p1 m1 \<and>
                  apply_to_distr snd \<mu> = denotation p2 m2 \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
using assms unfolding rhoare_def by simp


fun list_pattern_untyped :: "variable_untyped list \<Rightarrow> pattern_untyped" where
  "list_pattern_untyped [] = pattern_ignore unit_type"
| "list_pattern_untyped (x#xs) = pair_pattern_untyped (pattern_1var x) (list_pattern_untyped xs)"

definition "memory_pattern_related p1 p2 m1 m2 = (\<exists>v. m1 = memory_update_pattern m1 p1 v \<and> m2 = memory_update_pattern m2 p2 v)"


definition kill_vars_pattern :: "'a pattern \<Rightarrow> variable_untyped set \<Rightarrow> 'a pattern" where
  "kill_vars_pattern = undefined"

lemma memory_update_pattern_twice_kill: 
  "memory_update_pattern (memory_update_pattern m p x) q y = 
   memory_update_pattern (memory_update_pattern m (kill_vars_pattern p (set (p_vars q))) x) q y"
  sorry

lemma memory_update_pattern_twice [simp]: "memory_update_pattern (memory_update_pattern m p x) p y = memory_update_pattern m p y"
  sorry

lemma memory_pattern_relatedI: "m1 = memory_update_pattern m1' p1 v \<Longrightarrow> m2 = memory_update_pattern m2' p2 v \<Longrightarrow> memory_pattern_related p1 p2 m1 m2"
  unfolding memory_pattern_related_def by auto

(* lemma memory_pattern_related_unit_pattern [simp]: "memory_pattern_related unit_pattern unit_pattern m1 m2"
  unfolding memory_pattern_related_def memory_update_unit_pattern by auto *)

lemma memory_pattern_related_variable_pattern [simp]: 
  "memory_pattern_related (variable_pattern x) (variable_pattern y) m1 m2 = (memory_lookup m1 x = memory_lookup m2 y)"
  unfolding memory_pattern_related_def memory_update_variable_pattern
  by (metis memory_update_lookup memory_lookup_update_same)


lemma memory_update_pattern_swap: "memory_update_pattern (memory_update_pattern m a x) b y
     = memory_update_pattern (memory_update_pattern m b y) (kill_vars_pattern a (set (p_vars b))) x"
     sorry

lemma memory_pattern_related_pair_pattern [simp]: 
  "memory_pattern_related (pair_pattern a1 a2) (pair_pattern b1 b2) m1 m2
     = (memory_pattern_related a2 b2 m1 m2 
     \<and> memory_pattern_related (kill_vars_pattern a1 (set (p_vars a2))) (kill_vars_pattern b1 (set (p_vars b2))) m1 m2)" (is "?lhs=?rhs")
proof (rule iffI)
  assume "memory_pattern_related (pair_pattern a1 a2) (pair_pattern b1 b2) m1 m2"
  then obtain a b where m1: "m1 = memory_update_pattern (memory_update_pattern m1 a1 a) a2 b" and
        m2: "m2 = memory_update_pattern (memory_update_pattern m2 b1 a) b2 b"
  unfolding memory_pattern_related_def split_paired_Ex memory_update_pair_pattern by auto
  have "memory_pattern_related a2 b2 m1 m2"
    apply (rule memory_pattern_relatedI)
     close (subst m1, rule refl)
    by (subst m2, rule refl)

  moreover have "memory_pattern_related (kill_vars_pattern a1 (p_vars a2)) (kill_vars_pattern b1 (p_vars b2)) m1 m2"
    apply (rule memory_pattern_relatedI)
     apply (subst memory_update_pattern_swap[symmetric])
     close (subst m1, rule refl)
    apply (subst memory_update_pattern_swap[symmetric])
    by (subst m2, rule refl)

  ultimately show "?rhs" by simp
next
  assume "?rhs"
  hence 2: "memory_pattern_related a2 b2 m1 m2" and 1: "memory_pattern_related (kill_vars_pattern a1 (p_vars a2)) (kill_vars_pattern b1 (p_vars b2)) m1 m2"
    by simp_all
  from 2 obtain v where m1a2: "m1 = memory_update_pattern m1 a2 v" and m2b2: "m2 = memory_update_pattern m2 b2 v"
    unfolding memory_pattern_related_def by auto
  from 1 obtain w where m1a1: "m1 = memory_update_pattern m1 (kill_vars_pattern a1 (p_vars a2)) w" and
          m2b1: "m2 = memory_update_pattern m2 (kill_vars_pattern b1 (p_vars b2)) w"
    unfolding memory_pattern_related_def by auto
  have "m1 = memory_update_pattern m1 (pair_pattern a1 a2) (w,v)"
    unfolding memory_update_pair_pattern 
    apply (subst memory_update_pattern_twice_kill[of _ a1 _ a2])
    apply (subst m1a2) apply (subst m1a1) by simp
  moreover have "m2 = memory_update_pattern m2 (pair_pattern b1 b2) (w,v)"
    unfolding memory_update_pair_pattern 
    apply (subst memory_update_pattern_twice_kill[of _ b1 _ b2])
    apply (subst m2b2) apply (subst m2b1) by simp
  ultimately show "memory_pattern_related (pair_pattern a1 a2) (pair_pattern b1 b2) m1 m2"
    by (rule memory_pattern_relatedI)
qed

lemma memory_pattern_related_ignore_pattern1 [simp]: 
  "memory_pattern_related ignore_pattern p m1 m2"
  sorry

lemma memory_pattern_related_ignore_pattern2 [simp]: 
  "memory_pattern_related p ignore_pattern m1 m2"
  sorry

lemma kill_vars_pattern_pair_pattern [simp]: "kill_vars_pattern (pair_pattern p q) V = pair_pattern (kill_vars_pattern p V) (kill_vars_pattern q V)"
  sorry
(* lemma kill_vars_pattern_unit_pattern [simp]: "kill_vars_pattern (unit_pattern) V = unit_pattern"
  sorry *)
lemma kill_vars_pattern_ignore_pattern [simp]: "kill_vars_pattern (ignore_pattern) V = ignore_pattern"
  sorry
lemma kill_vars_pattern_variable_pattern1 [simp]: 
  "mk_variable_untyped x \<in> V \<Longrightarrow> kill_vars_pattern (variable_pattern x) V = ignore_pattern"
  sorry
lemma kill_vars_pattern_variable_pattern2 [simp]: 
  "mk_variable_untyped x \<notin> V \<Longrightarrow> kill_vars_pattern (variable_pattern x) V = variable_pattern x"
  sorry

lemma
  assumes "mk_variable_untyped x \<noteq> mk_variable_untyped y"
  assumes "mk_variable_untyped y \<noteq> mk_variable_untyped x"
  assumes "mk_variable_untyped x \<noteq> mk_variable_untyped z"
  assumes "mk_variable_untyped z \<noteq> mk_variable_untyped x"
  assumes "mk_variable_untyped z \<noteq> mk_variable_untyped y"
  assumes "mk_variable_untyped y \<noteq> mk_variable_untyped z"
  assumes "mk_variable_untyped z \<noteq> mk_variable_untyped a"
  shows "memory_pattern_related (pair_pattern (variable_pattern x) (pair_pattern (variable_pattern y) (variable_pattern z))) (pair_pattern (variable_pattern z) (pair_pattern (variable_pattern a) ignore_pattern)) m1 m2"
  apply (auto simp: assms)
oops

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

(* TODO: use callproc_equiv and transitivity for some callproc_subst-variant below *)

lemma callproc_subst:
  fixes x1::"'x1::prog_type pattern" and x2::"'x2::prog_type pattern" and y1 y2 and x1e::"'x1 expression" and x2e::"'x2 expression"
  assumes p: "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<exists>m1' m2'.
            ((\<forall>v\<in>V1. memory_lookup_untyped m1 v = memory_lookup_untyped m1' v) \<and> e_fun y1 m1 = e_fun y1' m1'
             \<and> P' m1' m2' \<and> 
             (\<forall>v\<in>V1. memory_lookup_untyped m2 v = memory_lookup_untyped m2' v) \<and> e_fun y1 m2 = e_fun y1' m2')"
  assumes rhoare: "rhoare P' (callproc x1' f1 y1') (callproc x2' f2 y2') Q'"
  shows "rhoare P (callproc x1 f1 y1) (callproc x2 f2 y2) Q"
proof -
  have rhoare1: 
      "rhoare (\<lambda>m1 m1'. (\<forall>v\<in>V1. memory_lookup_untyped m1 v = memory_lookup_untyped m1' v) \<and> e_fun y1 m1 = e_fun y1' m1') 
          (callproc x1 f1 y1) (callproc x1' f1 y1')
          (\<lambda>m1 m1'. (\<forall>v\<in>V2. memory_lookup_untyped m1 v = memory_lookup_untyped m1' v)
                      \<and> memory_pattern_related x1 x1' m1 m1')"
    apply (rule callproc_equiv)
    by later
  show ?thesis
    apply (rule rtrans3_rule[OF _ _ _ rhoare])
    defer defer
    apply (rule callproc_equiv)
    prefer 5
    apply (rule callproc_equiv)
    
    

lemma callproc_subst:
  fixes x1::"'x1::prog_type pattern" and x2::"'x2::prog_type pattern" and y1 y2 and x1e::"'x1 expression" and x2e::"'x2 expression"
  assumes rhoare: "rhoare P' (callproc x1' f1 y1') (callproc x2' f2 y2') Q'"
  shows "rhoare P (callproc x1 f1 y1) (callproc x2 f2 y2) Q"
proof (rule rhoareI, goal_cases)
case (1 m1 m2)
  fix in1 in2 (* TODO define *)
  def m1' == "in1 m1 :: memory" and m2' == "in2 m2 :: memory"
  have P': "P' m1' m2'" by later
  obtain \<mu>' where fst': "apply_to_distr fst \<mu>' = denotation (callproc x1' f1 y1') m1'"
              and snd': "apply_to_distr snd \<mu>' = denotation (callproc x2' f2 y2') m2'"
              and supp': "\<And>m1'f m2'f. (m1'f,m2'f) \<in> support_distr \<mu>' \<Longrightarrow> Q' m1'f m2'f"
    apply atomize_elim using P' by (rule rhoare[THEN rhoareE])
  fix out1 out2 (* TODO define *)

  have Q'_Q: "\<And>x y. Q' x y \<Longrightarrow> Q (out1 x) (out2 y)" by later
  def \<mu> == "apply_to_distr (\<lambda>(m1f,m2f). (out1 m1f, out2 m2f)) \<mu>' :: (memory\<times>memory) distr"

  have y1'y1: "e_fun y1' m1' = e_fun y1 m1" by auto
  have rel1: "denotation (callproc x1 f1 y1) m1 = apply_to_distr out1 (denotation (callproc x1' f1 y1') m1')" 
    unfolding denotation_callproc y1'y1 Let_def 
    unfolding apply_to_distr_twice
    unfolding m1'_def
    apply (tactic \<open>cong_tac @{context} 1\<close>; (rule refl)?)+

by later
  hence fst: "apply_to_distr fst \<mu> = denotation (callproc x1 f1 y1) m1" 
    unfolding \<mu>_def split_def using fst'[THEN arg_cong[where f="apply_to_distr out1"]] by auto
  have rel2: "denotation (callproc x2 f2 y2) m2 = apply_to_distr out2 (denotation (callproc x2' f2 y2') m2')" by later
  hence snd: "apply_to_distr snd \<mu> = denotation (callproc x2 f2 y2) m2"
    unfolding \<mu>_def split_def using snd'[THEN arg_cong[where f="apply_to_distr out2"]] by auto
  have supp: "\<And>m1f m2f. (m1f,m2f) \<in> support_distr \<mu> \<Longrightarrow> Q m1f m2f" 
    unfolding \<mu>_def using supp' by (auto intro!: Q'_Q)
  from fst snd supp show ?case by auto
qed

lemma callproc_subst:
  fixes x1::"'x1::prog_type pattern" and x2::"'x2::prog_type pattern" and y1 y2 and x1e::"'x1 expression" and x2e::"'x2 expression"
  assumes "rhoare P
              (callproc (variable_pattern res) f1 (var_expression args))
              (callproc (variable_pattern res) f2 (var_expression args))
              Q"
  defines "P' == \<lambda>m1 m2. P (memory_update m1 args (e_fun y1 m1)) (memory_update m2 args (e_fun y2 m2))"
  defines "Q' == \<lambda>m1 m2. Q (memory_update m1 res (e_fun x1e m1)) (memory_update m2 res (e_fun x2e m2))"
  shows "rhoare P' (callproc x1 f1 y1) (callproc x2 f2 y2) Q'"
proof -
  (* Proof plan: 

  - V=globals \<union> res, arg, footprint

  - callproc x1=f1(y1)    obseq(V)    "unfolding of it"
  - callproc x2=f2(y2)    obseq(V)    "unfolding of it"
  - callproc res=f1(args) obseq(V)    "unfolding of it"
  - callproc res=f2(args) obseq(V)    "unfolding of it"

  - rhoare P (res=f1(args)) ... Q  \<Longrightarrow>  rhoare P (unfold res=f1(args)) ... Q   (uses footprint P,Q in V)
  - rhoare P (unfold res=f1(args)) ... Q   \<Longrightarrow>   rhoare P' (unfold x1=f1(y1)) ... Q'   (using wp, sp etc)
  - rhoare P' (unfold x1=f1(y1)) ... Q'  \<Longrightarrow>  rhoare P' (x1=f1(y1)) .. Q'    (footprint P,Q in V)

  Constraints on V: 
  - contains all globals

  *)
thm callproc_rule
qed

lemma call_rule:
  fixes globals_f1 globals_f2 and x1::"'x1::prog_type pattern" and x2::"'x2::prog_type pattern" and y1 y2 A B P Q
  assumes "set(vars_proc_global f1) \<subseteq> set globals_f1"
  assumes "set(vars_proc_global f2) \<subseteq> set globals_f2"
  assumes "rhoare P
              (callproc (variable_pattern res) f1 (var_expression args))
              (callproc (variable_pattern res) f2 (var_expression args))
              Q"
  defines "QB == (\<lambda>m1 m2. (\<forall>gL gR xL xR. Q (memory_update (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f1) gL) res xL) 
                       (memory_update (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f2)  gL) res xR)
                \<longrightarrow> B (memory_update_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f1) gL) x1 xL) 
                      (memory_update_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f2) gL) x2 xR)))"
  defines "C == (\<lambda>m1 m2. P (memory_update m1 args (e_fun y1 m1)) (memory_update m2 args (e_fun y2 m2)) \<and> QB m1 m2)"
  assumes "rhoare A p1 p2 C"
  shows "rhoare A (seq p1 (callproc x1 f1 y1)) (seq p2 (callproc x2 f2 y2)) B"
proof -
  def x1e == "undefined::'x1 expression" def x2e == "undefined::'x2 expression" (* TODO *)
  def P' == "\<lambda>m1 m2. P (memory_update m1 args (e_fun y1 m1)) (memory_update m2 args (e_fun y2 m2))"
  def Q' == "\<lambda>m1 m2. Q (memory_update m1 res (e_fun x1e m1)) (memory_update m2 res (e_fun x2e m2))"

  have "obs_eq' V (callproc ?x ?p ?args)
     (seq (seq (seq (assign (p_arg ?p) ?args) (assign_default_typed ?non_parg_locals)) (p_body ?p)) (assign ?x (p_return ?p)))"
thm callproc_rule 

  have Q'_foot1: "assertion_footprint_left XXX Q'" sorry
  have Q'_foot2: "assertion_footprint_right YYY Q'" sorry

  have "rhoare P' (callproc x1 f1 y1) (callproc x2 f2 y2) Q'"
    using obseq_context_empty Q'_foot1 apply (rule rhoare_left_obseq_replace[where C="\<lambda>x. x"])
     apply (rule callproc_rule)
     close 6 (tactic "ALLGOALS (Skip_Proof.cheat_tac @{context})") (* sorry *)
    using obseq_context_empty Q'_foot2 apply (rule rhoare_right_obseq_replace[where C="\<lambda>x. x"])
     apply (rule callproc_rule)
     close 6 (tactic "ALLGOALS (Skip_Proof.cheat_tac @{context})") (* sorry *)
    
    find_theorems "obseq_context _ (\<lambda>x. x)" 
thm rhoare_left_obseq_replace
(* Proof plan: 

- Show:  rhoare    P{args/y}  (callproc x=f(y))  Q{x/res}    (substitution)
- Show:  footprint QB   disjoint of   callproc x=f(y)
- Show:  rhoare    C=P{args/y}\<and>QB     (callproc x=f(y))   Q{res/x}\<and>QB   (frame_rule)
- Show:  Q{res/x} \<and> QB \<Longrightarrow> Q
- Show:  rhoare    C     (callproc x=f(y))   Q    (conseq)
- Show:  rhoare    P     (p; callproc x=f(y))   Q    (seq with assm)

*)
find_theorems assertion_footprint
  show ?thesis sorry
qed


end