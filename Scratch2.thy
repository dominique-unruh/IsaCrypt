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

definition var_expression_untyped :: "variable_untyped \<Rightarrow> expression_untyped" where
"var_expression_untyped v = Abs_expression_untyped
  \<lparr> eur_fun=\<lambda>m. memory_lookup_untyped m v,
    eur_type=vu_type v,
    eur_vars=[v] \<rparr>"
lemma Rep_var_expression_untyped: "Rep_expression_untyped (var_expression_untyped v) = 
  \<lparr> eur_fun=\<lambda>m. memory_lookup_untyped m v,
    eur_type=vu_type v,
    eur_vars=[v] \<rparr>"
  unfolding var_expression_untyped_def
  apply (subst Abs_expression_untyped_inverse)
  by auto
lemma eu_type_var_expression_untyped [simp]: "eu_type (var_expression_untyped x) = vu_type x"
  unfolding eu_type_def using Rep_var_expression_untyped by simp
lemma eu_fun_var_expression_untyped [simp]: "eu_fun (var_expression_untyped x) = (\<lambda>m. memory_lookup_untyped m x)"
  unfolding eu_fun_def using Rep_var_expression_untyped by simp

lemma eu_fun_type [simp]: "eu_fun e m \<in> t_domain (eu_type e)"
  using Rep_expression_untyped eu_fun_def eu_type_def by auto

definition pair_expression_untyped :: "expression_untyped \<Rightarrow> expression_untyped \<Rightarrow> expression_untyped" where
  "pair_expression_untyped e1 e2 = Abs_expression_untyped
   \<lparr> eur_fun = (\<lambda>m. val_prod_embedding (eu_fun e1 m, eu_fun e2 m)),
     eur_type = prod_type (eu_type e1) (eu_type e2),
     eur_vars = eu_vars e1 @ eu_vars e2 \<rparr>"
lemma Rep_pair_expression_untyped: "Rep_expression_untyped (pair_expression_untyped e1 e2) =
   \<lparr> eur_fun = (\<lambda>m. val_prod_embedding (eu_fun e1 m, eu_fun e2 m)),
     eur_type = prod_type (eu_type e1) (eu_type e2),
     eur_vars = eu_vars e1 @ eu_vars e2 \<rparr>"
  unfolding pair_expression_untyped_def
  apply (subst Abs_expression_untyped_inverse)
  apply auto by (metis UnCI eu_fun_footprint)
lemma eu_fun_pair_expression_untyped: "eu_fun (pair_expression_untyped e1 e2) = (\<lambda>m. val_prod_embedding (eu_fun e1 m, eu_fun e2 m))"
  using Rep_pair_expression_untyped unfolding eu_fun_def by auto
lemma eu_type_pair_expression_untyped [simp]: "eu_type (pair_expression_untyped e1 e2) = prod_type (eu_type e1) (eu_type e2)"
  using Rep_pair_expression_untyped unfolding eu_type_def by auto

fun list_expression_untyped :: "variable_untyped list \<Rightarrow> expression_untyped" where
  "list_expression_untyped [] = const_expression_untyped unit_type (embedding (default::unit))"
| "list_expression_untyped (x#xs) = pair_expression_untyped (var_expression_untyped x) (list_expression_untyped xs)"

fun list_pattern_untyped :: "variable_untyped list \<Rightarrow> pattern_untyped" where
  "list_pattern_untyped [] = pattern_ignore unit_type"
| "list_pattern_untyped (x#xs) = pair_pattern_untyped (pattern_1var x) (list_pattern_untyped xs)"

lemma pu_vars_list_pattern_untyped [simp]: "pu_vars (list_pattern_untyped xs) = xs"
  apply (induction xs) by auto

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

  moreover have "memory_pattern_related (kill_vars_pattern a1 (set (p_vars a2))) (kill_vars_pattern b1 (set (p_vars b2))) m1 m2"
    apply (rule memory_pattern_relatedI)
     apply (subst memory_update_pattern_swap[symmetric])
     close (subst m1, rule refl)
    apply (subst memory_update_pattern_swap[symmetric])
    by (subst m2, rule refl)

  ultimately show "?rhs" by simp
next
  assume "?rhs"
  hence 2: "memory_pattern_related a2 b2 m1 m2" and 1: "memory_pattern_related (kill_vars_pattern a1 (set (p_vars a2))) (kill_vars_pattern b1 (set (p_vars b2))) m1 m2"
    by simp_all
  from 2 obtain v where m1a2: "m1 = memory_update_pattern m1 a2 v" and m2b2: "m2 = memory_update_pattern m2 b2 v"
    unfolding memory_pattern_related_def by auto
  from 1 obtain w where m1a1: "m1 = memory_update_pattern m1 (kill_vars_pattern a1 (set (p_vars a2))) w" and
          m2b1: "m2 = memory_update_pattern m2 (kill_vars_pattern b1 (set (p_vars b2))) w"
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



(*
lemma callproc_subst:
  fixes x1::"'x1::prog_type pattern" and x2::"'x2::prog_type pattern" and y1 y2 and x1e::"'x1 expression" and x2e::"'x2 expression"
  assumes rhoare: "rhoare P' (callproc x1' f1 y1') (callproc x2' f2 y2') Q'"
  shows "rhoare P (callproc x1 f1 y1) (callproc x2 f2 y2) Q"
apply (rule rtrans_rule) defer defer 
apply (rule rtrans_rule) defer defer defer
apply (fact rhoare)
apply (rule callproc_equiv)  defer defer defer defer defer defer defer defer
apply (rule callproc_equiv)
*)

(*
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
oops    
*)  

(*
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
oops

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
oops
*)

lemma assertion_footprint_leftE: 
  "assertion_footprint_left X P \<Longrightarrow> (\<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m1' x) \<Longrightarrow> (m2::memory)=m2' \<Longrightarrow> P m1 m2 = P m1' m2'"
unfolding assertion_footprint_left_def by simp
lemma assertion_footprint_rightE:
   "assertion_footprint_right X P \<Longrightarrow> (\<forall>x\<in>X. memory_lookup_untyped m2 x = memory_lookup_untyped m2' x) \<Longrightarrow> (m1::memory)=m1' \<Longrightarrow> P m1 m2 = P m1' m2'"
unfolding assertion_footprint_right_def by simp

lemma program_readonly_mono:
  assumes mono: "A \<le> B"
  assumes foot: "program_readonly B d"
  shows "program_readonly A d"
by (meson denotation_readonly_def foot mono program_readonly_def subset_iff)

lemma assertion_footprint_left_update_pattern:
  assumes "Y \<subseteq> X \<union> set (p_vars pat)"
  assumes "assertion_footprint_left Y P"
  shows "assertion_footprint_left X (\<lambda>m m'. P (memory_update_pattern m pat x) m')"
unfolding memory_update_pattern_def
apply (rule assertion_footprint_left_update_pattern_untyped)
using assms unfolding p_vars_def by auto

lemma assertion_footprint_left_update:
  assumes "Y \<subseteq> insert (mk_variable_untyped x) X"
  assumes "assertion_footprint_left Y P"
  shows "assertion_footprint_left X (\<lambda>m m'. P (memory_update m x v) m')"
unfolding memory_update_def
apply (rule assertion_footprint_left_update_untyped)
using assms by auto

lemma assertion_footprint_right_update_pattern:
  assumes "Y \<subseteq> X \<union> set (p_vars pat)"
  assumes "assertion_footprint_right Y P"
  shows "assertion_footprint_right X (\<lambda>m m'. P m (memory_update_pattern m' pat x))"
unfolding memory_update_pattern_def
apply (rule assertion_footprint_right_update_pattern_untyped)
using assms unfolding p_vars_def by auto

lemma assertion_footprint_right_update:
  assumes "Y \<subseteq> insert (mk_variable_untyped x) X"
  assumes "assertion_footprint_right Y P"
  shows "assertion_footprint_right X (\<lambda>m m'. P m (memory_update m' x v))"
unfolding memory_update_def
apply (rule assertion_footprint_right_update_untyped)
using assms by auto

lemma memory_lookup_inject: "memory_lookup_untyped m = memory_lookup_untyped m' \<Longrightarrow> m=m'"
  apply (cases m, cases m', simp)
  apply (subst (asm) Abs_memory_inverse) close simp
  apply (subst (asm) Abs_memory_inverse) close simp
  by simp

lemma assertion_footprint_left_UNIV: 
  shows "assertion_footprint_left UNIV P"
    unfolding assertion_footprint_left_def
    using memory_lookup_inject[OF ext] by auto

lemma assertion_footprint_right_UNIV: 
  shows "assertion_footprint_right UNIV P"
    unfolding assertion_footprint_right_def
    using memory_lookup_inject[OF ext] by auto

lemma assertion_footprint_left_mono:
  assumes "X \<subseteq> Y"
  assumes "assertion_footprint_left X P"
  shows   "assertion_footprint_left Y P"
using assms unfolding assertion_footprint_left_def by blast

lemma assertion_footprint_right_mono:
  assumes "X \<subseteq> Y"
  assumes "assertion_footprint_right X P"
  shows   "assertion_footprint_right Y P"
using assms unfolding assertion_footprint_right_def by blast

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

end