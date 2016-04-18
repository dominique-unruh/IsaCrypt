theory Scratch2
imports Main Hoare_Tactics Procs_Typed RHL_Typed
begin

lemma rhoare_untypedE: 
  assumes "rhoare_untyped P p1 p2 Q"
  assumes "P m1 m2"
  shows "\<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped p1 m1 \<and>
                  apply_to_distr snd \<mu> = denotation_untyped p2 m2 \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
using assms unfolding rhoare_untyped_rhoare_denotation rhoare_denotation_def by simp

lemma rhoareE: 
  assumes "rhoare P p1 p2 Q"
  assumes "P m1 m2"
  shows "\<exists>\<mu>. apply_to_distr fst \<mu> = denotation p1 m1 \<and>
                  apply_to_distr snd \<mu> = denotation p2 m2 \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
using assms unfolding rhoare_def by simp

lemma memory_update_pattern_untyped_swap: "memory_update_untyped_pattern (memory_update_untyped_pattern m a x) b y
     = memory_update_untyped_pattern (memory_update_untyped_pattern m b y) (kill_vars_pattern_untyped a (set (pu_vars b))) x"
     sorry

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

lemma callproc_split_result: 
  assumes footQ1: "assertion_footprint_left (-{mk_variable_untyped x1}) Q"
  assumes footQ2: "assertion_footprint_right (-{mk_variable_untyped x2}) Q"
  assumes rh: "rhoare P (seq (seq c1 (callproc (variable_pattern x1) f1 e1)) (assign p1 (var_expression x1)))
                        (seq (seq c2 (callproc (variable_pattern x2) f2 e2)) (assign p2 (var_expression x2))) Q"
  shows "rhoare P (seq c1 (callproc p1 f1 e1)) (seq c2 (callproc p2 f2 e2)) Q"
proof -
  let ?x1 = "mk_variable_untyped x1"
  let ?x2 = "mk_variable_untyped x2"
  def eq == "\<lambda>X m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  have aux: "(\<lambda>mem1 mem2. eq X mem2 mem1) = (eq X)" for X unfolding eq_def by force

  have "rhoare (eq UNIV) (callproc p1 f1 e1) (seq (callproc (variable_pattern x1) f1 e1) (assign p1 (var_expression x1))) (eq (-{?x1}))"
    unfolding eq_def obs_eq_def[symmetric]
    by (rule callproc_split_result_equiv, auto)
  hence left: "rhoare (eq UNIV) 
            (seq c1 (callproc p1 f1 e1)) 
            (seq c1 ((seq (callproc (variable_pattern x1) f1 e1) (assign p1 (var_expression x1))))) 
         (eq (-{?x1}))"
    apply (rule rseq_rule[rotated])
    unfolding eq_def obs_eq_def[symmetric]
    by (rule self_obseq_vars, auto)

  have "rhoare (eq UNIV) (callproc p2 f2 e2) (seq (callproc (variable_pattern x2) f2 e2) (assign p2 (var_expression x2))) (eq (-{?x2}))"
    unfolding eq_def obs_eq_def[symmetric]
    by (rule callproc_split_result_equiv, auto)
  hence "rhoare (eq UNIV) (seq (callproc (variable_pattern x2) f2 e2) (assign p2 (var_expression x2))) (callproc p2 f2 e2) (eq (-{?x2}))"
    apply (rule_tac rsymmetric_rule) 
    unfolding aux by simp
  hence right: "rhoare (eq UNIV) (seq c2 (seq (callproc (variable_pattern x2) f2 e2) (assign p2 (var_expression x2))))
                                 (seq c2 (callproc p2 f2 e2))     (eq (-{?x2}))"
    apply (rule rseq_rule[rotated])
    unfolding eq_def obs_eq_def[symmetric]
    by (rule self_obseq_vars, auto)

  have mid: "rhoare P (seq c1 (seq (callproc (variable_pattern x1) f1 e1) (assign p1 (var_expression x1))))
                      (seq c2 (seq (callproc (variable_pattern x2) f2 e2) (assign p2 (var_expression x2)))) Q"
    using rh by (simp add: seq_assoc_left_rule seq_assoc_right_rule)

  show ?thesis
    apply (rule rtrans3_rule[rotated 2])
        close (fact left) close (fact mid) close (fact right)
     unfolding eq_def 
     using footQ1 footQ2 close blast
    using assertion_footprint_leftE assertion_footprint_rightE footQ1 footQ2 by fastforce
qed

lemma callproc_split_args: 
  assumes footQ1: "assertion_footprint_left (-{mk_variable_untyped x1}) Q"
  assumes footQ2: "assertion_footprint_right (-{mk_variable_untyped x2}) Q"
  assumes x1f1: "mk_variable_untyped x1 \<notin> set (vars_proc_global f1)"
  assumes x1e1: "mk_variable_untyped x1 \<notin> set (e_vars e1)"
  assumes x2f2: "mk_variable_untyped x2 \<notin> set (vars_proc_global f2)"
  assumes x2e2: "mk_variable_untyped x2 \<notin> set (e_vars e2)"
  assumes rh: "rhoare P (seq (seq c1 (assign (variable_pattern x1) e1)) (callproc p1 f1 (var_expression x1)))
                        (seq (seq c2 (assign (variable_pattern x2) e2)) (callproc p2 f2 (var_expression x2))) Q"
  shows "rhoare P (seq c1 (callproc p1 f1 e1)) (seq c2 (callproc p2 f2 e2)) Q"
proof -
  let ?x1 = "mk_variable_untyped x1"
  let ?x2 = "mk_variable_untyped x2"
  def eq == "\<lambda>X m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  have aux: "(\<lambda>mem1 mem2. eq X mem2 mem1) = (eq X)" for X unfolding eq_def by force

  have "rhoare (eq (-{?x1})) (callproc p1 f1 e1) (seq (assign (variable_pattern x1) e1) (callproc p1 f1 (var_expression x1))) (eq (-{?x1}))"
    unfolding eq_def obs_eq_def[symmetric]
    by (rule callproc_split_args_equiv, auto simp: x1f1 x1e1)
  hence left: "rhoare (eq UNIV) 
            (seq c1 (callproc p1 f1 e1)) 
            (seq c1 (seq (assign (variable_pattern x1) e1) (callproc p1 f1 (var_expression x1))))
         (eq (-{?x1}))"
    apply (rule rseq_rule[rotated])
    unfolding eq_def obs_eq_def[symmetric]
    by (rule self_obseq_vars, auto)

  have "rhoare (eq (-{?x2})) (callproc p2 f2 e2) (seq (assign (variable_pattern x2) e2) (callproc p2 f2 (var_expression x2))) (eq (-{?x2}))"
    unfolding eq_def obs_eq_def[symmetric]
    by (rule callproc_split_args_equiv, auto simp: x2f2 x2e2)
  hence "rhoare (eq (-{?x2})) (seq (assign (variable_pattern x2) e2) (callproc p2 f2 (var_expression x2))) (callproc p2 f2 e2) (eq (-{?x2}))"
    apply (rule_tac rsymmetric_rule) 
    unfolding aux by simp
  hence right: "rhoare (eq UNIV) (seq c2 (seq (assign (variable_pattern x2) e2) (callproc p2 f2 (var_expression x2))))
                                 (seq c2 (callproc p2 f2 e2))     (eq (-{?x2}))"
    apply (rule rseq_rule[rotated])
    unfolding eq_def obs_eq_def[symmetric]
    by (rule self_obseq_vars, auto)

  have mid: "rhoare P (seq c1 (seq (assign (variable_pattern x1) e1) (callproc p1 f1 (var_expression x1))))
                      (seq c2 (seq (assign (variable_pattern x2) e2) (callproc p2 f2 (var_expression x2)))) Q"
    using rh by (simp add: seq_assoc_left_rule seq_assoc_right_rule)

  show ?thesis
    apply (rule rtrans3_rule[rotated 2])
        close (fact left) close (fact mid) close (fact right)
     unfolding eq_def 
    using footQ1 footQ2
    by (auto simp: assertion_footprint_leftE assertion_footprint_rightE)
qed

lemma kill_vars_pattern_untyped_disjoint:
  assumes "set (pu_vars p) \<inter> X = {}"
  shows "kill_vars_pattern_untyped p X = p"
sorry

lemma list_expression_list_pattern_untyped:
  assumes "distinct x"
  assumes "v \<in> t_domain (pu_type (list_pattern_untyped x))"
  shows "eu_fun (list_expression_untyped x) (memory_update_untyped_pattern m (list_pattern_untyped x) v) = v"
using assms proof (induction x arbitrary: m v)
case Nil thus ?case by (simp add: eu_fun_const_expression_untyped)
next case (Cons x xs)
  obtain u w where v: "v = val_prod_embedding (u,w)" apply atomize_elim using Cons.prems by auto
  have u: "u \<in> t_domain (pu_type (pattern_1var x))"
    by (smt Cons.prems(2) imageE inj_val_prod_embedding inv_f_f list_pattern_untyped.simps(2) mem_Sigma_iff pu_type_pair_pattern t_domain_prod v)
  have w: "w \<in> t_domain (pu_type (list_pattern_untyped xs))"
    by  (smt Cons.prems(2) imageE inj_val_prod_embedding inv_f_f list_pattern_untyped.simps(2) mem_Sigma_iff pu_type_pair_pattern t_domain_prod v)

  have t1: "memory_lookup_untyped (memory_update_untyped_pattern (memory_update_untyped_pattern m
            (pattern_1var x) u) (list_pattern_untyped xs) w) x = u"
    apply (subst memory_lookup_update_pattern_notsame)
     using Cons.prems memory_lookup_update_same_untyped u by auto

  show "eu_fun (list_expression_untyped (x # xs)) (memory_update_untyped_pattern m (list_pattern_untyped (x # xs)) v)
      = v"
    apply (simp add: eu_fun_pair_expression_untyped v)
    apply (subst memory_update_pair_pattern_untyped[OF u w])
    apply (subst memory_update_pair_pattern_untyped[OF u w])
    apply (subst Cons.IH)
      using Cons w close 2
    apply (subst t1)
    by rule
qed  

find_theorems list_expression_untyped pu_type

thm call_rule

(* TODO: cleanup premises *)
lemma call_rule_abstract: 
  fixes globals_f and res x1 x2::"'x::prog_type variable" 
    and args y1 y2::"'y::prog_type variable"
    and A B 
  assumes distinct: "distinct globals_f"
  assumes globals_f: "set(write_vars_proc_global f) \<subseteq> set globals_f"
  assumes globals_f': "set(vars_proc_global f) \<supseteq> set globals_f"
  assumes x1_globals: "mk_variable_untyped x1 \<notin> set globals_f"
  assumes x2_globals: "mk_variable_untyped x2 \<notin> set globals_f"
  assumes res_nin_f: "mk_variable_untyped res \<notin> set (vars_proc_global f)"
  assumes args_nin_f: "mk_variable_untyped args \<notin> set (vars_proc_global f)"
  assumes args_not_res: "mk_variable_untyped args \<noteq> mk_variable_untyped res"
(*   defines "P' == \<lambda>m1 m2. \<forall>x\<in>set (vars_proc_global f) \<union> {mk_variable_untyped res, mk_variable_untyped args}.
                    memory_lookup_untyped m1 x = memory_lookup_untyped m2 x" *)
(*  defines "QB' == (\<lambda>m1 m2. (\<forall>gL gR xL xR x'L x'R. 
                     (xL = xR \<and> gL = gR) 
                \<longrightarrow> B (memory_update (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) x1 xL)
                      (memory_update (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR) x2 xR)))" *)
  defines "QB' == (\<lambda>m1 m2. (\<forall>g x. 
                B (memory_update (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) g) x1 x)
                  (memory_update (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) g) x2 x)))"
  (* defines "C' == (\<lambda>m1 m2. P' (memory_update m1 args (memory_lookup m1 y1)) (memory_update m2 args (memory_lookup m2 y2)) \<and> QB' m1 m2)" *)
  defines "C' == (\<lambda>m1 m2. 
      (\<forall>x\<in>set (vars_proc_global f). memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)
    \<and> memory_lookup m1 y1 = memory_lookup m2 y2
    \<and> memory_lookup m1 res = memory_lookup m2 res (* TODO: Why do we need this one? res will be overwritten! *)
    \<and> QB' m1 m2)"
  assumes p1p2': "rhoare A p1 p2 C'"
  shows "rhoare A (seq p1 (callproc (variable_pattern x1) f (var_expression y1))) 
                  (seq p2 (callproc (variable_pattern x2) f (var_expression y2))) B"
proof -
  def Q == "\<lambda>m1 m2. \<forall>x\<in>set (vars_proc_global f) \<union> {mk_variable_untyped res}. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  def QB == "\<lambda>m1 m2. (\<forall>gL gR xL xR x'L x'R. gL \<in> t_domain (pu_type (list_pattern_untyped globals_f)) \<longrightarrow>
                 gR \<in> t_domain (pu_type (list_pattern_untyped globals_f)) \<longrightarrow>
                     Q (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) (list_pattern_untyped (p_vars (variable_pattern x1))) x'L) res xL)
                       (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR) (list_pattern_untyped (p_vars (variable_pattern x2))) x'R) res xR)
                \<longrightarrow> B (memory_update_pattern
                     (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) (variable_pattern x1) xL)
                  (memory_update_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR)
                    (variable_pattern x2) xR))"
  def P == "\<lambda>m1 m2. \<forall>x\<in>set (vars_proc_global f) \<union> {mk_variable_untyped res, mk_variable_untyped args}.
                    memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  def C == "\<lambda>m1 m2. P (memory_update m1 args (e_fun (var_expression y1) m1))
              (memory_update m2 args (e_fun (var_expression y2) m2)) \<and> QB m1 m2"


  have Q': "gL = gR \<and> xL = xR" 
    if gL_type: "gL \<in> t_domain (pu_type (list_pattern_untyped globals_f))"
    and gR_type: "gR \<in> t_domain (pu_type (list_pattern_untyped globals_f))" 
    and Q: "Q (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) (list_pattern_untyped (p_vars (variable_pattern x1))) x'L) res xL)
           (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR) (list_pattern_untyped (p_vars (variable_pattern x2))) x'R) res xR)"
            (is "Q ?ml ?mr")
    for m1 m2 gL gR x'L x'R xL xR 
  proof -
    def ml == ?ml def mr == ?mr
    note Q_rule = Q[unfolded Q_def, rule_format]
    note Q_rule' = Q[folded ml_def mr_def, unfolded Q_def, rule_format]

    have xLxR: "xL = xR" 
      using Q_rule[of "mk_variable_untyped res"] by auto
    
    have kill_x1: "kill_vars_pattern_untyped (list_pattern_untyped globals_f) {mk_variable_untyped x1} = list_pattern_untyped globals_f"
      apply (rule kill_vars_pattern_untyped_disjoint) using x1_globals by simp
    have kill_x2: "kill_vars_pattern_untyped (list_pattern_untyped globals_f) {mk_variable_untyped x2} = list_pattern_untyped globals_f"
      apply (rule kill_vars_pattern_untyped_disjoint) using x2_globals by simp
    have kill_res: "kill_vars_pattern_untyped (list_pattern_untyped globals_f) {mk_variable_untyped res} = list_pattern_untyped globals_f"
      apply (rule kill_vars_pattern_untyped_disjoint) using globals_f' res_nin_f by auto

    have swapL: "memory_update (memory_update_untyped_pattern m (list_pattern_untyped globals_f) gL) res xL
               = memory_update_untyped_pattern (memory_update m res xL) (list_pattern_untyped globals_f) gL" for m
      unfolding memory_update_def
      apply (subst memory_update_untyped_pattern_1var[symmetric]) close simp
      unfolding memory_update_pattern_untyped_swap[where a="list_pattern_untyped globals_f"]
      by (auto simp: kill_res)
    have swapR: "memory_update (memory_update_untyped_pattern m (list_pattern_untyped globals_f) gR) res xR
               = memory_update_untyped_pattern (memory_update m res xR) (list_pattern_untyped globals_f) gR" for m
      unfolding memory_update_def
      apply (subst memory_update_untyped_pattern_1var[symmetric]) close simp
      unfolding memory_update_pattern_untyped_swap[where a="list_pattern_untyped globals_f"]
      by (auto simp: kill_res)

    have "eu_fun (list_expression_untyped globals_f) ml = eu_fun (list_expression_untyped globals_f) mr"
      apply (rule eu_fun_footprint)
      using Q_rule' globals_f' by auto
    hence gLgR: "gL = gR"
      unfolding mr_def ml_def apply simp
      unfolding memory_update_pattern_untyped_swap[where a="list_pattern_untyped globals_f"]
      apply (simp add: kill_x1 kill_x2)
      unfolding swapL swapR
      apply (subst (asm) list_expression_list_pattern_untyped)
        using distinct gL_type close 2
      apply (subst (asm) list_expression_list_pattern_untyped)
        using distinct gR_type close 2
      by simp
    show ?thesis using xLxR gLgR by simp
  qed

  have B': "B (memory_update_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) (variable_pattern x1) xL)
        (memory_update_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR) (variable_pattern x2) xR)"
        if "B (memory_update (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) x1 xL)
              (memory_update (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR) x2 xR)" for gL gR m1 m2 xL xR
    by (simp add: that)

  have QB'QB: "QB' m1 m2 \<Longrightarrow> QB m1 m2" for m1 m2
    unfolding QB'_def QB_def
    apply rule+
    apply (drule_tac Q')
      close 2 simp_all
    apply (rule B')
    by simp
          
  have P'P: "P (memory_update m1 args (memory_lookup m2 y2)) (memory_update m2 args (memory_lookup m2 y2))"
        if "\<forall>x\<in>set (vars_proc_global f). memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
        and "memory_lookup m1 y1 = memory_lookup m2 y2"
        and "memory_lookup m1 res = memory_lookup m2 res" for m1 m2
    unfolding P_def using that by auto

  from QB'QB P'P have "C' m1 m2 \<Longrightarrow> C m1 m2" for m1 m2 unfolding C'_def C_def by simp
  hence p1p2: "rhoare A p1 p2 C"
    apply (rule_tac rconseq_rule[OF _ _ p1p2'])
    by auto

  have "obs_eq (set(vars_proc_global f) \<union> {mk_variable_untyped res, mk_variable_untyped args})  
      (set(vars_proc_global f) \<union> {mk_variable_untyped res}) 
      (callproc (variable_pattern res) f (var_expression args)) (callproc (variable_pattern res) f (var_expression args))"
    by (rule self_obseq_vars, auto)
  hence PfQ: "rhoare P (callproc (variable_pattern res) f (var_expression args))
                 (callproc (variable_pattern res) f (var_expression args)) Q"
    unfolding obs_eq_def P_def Q_def by simp

  have footQ1: "assertion_footprint_left (- {mk_variable_untyped args}) Q"
    unfolding Q_def
    apply (rule assertion_footprint_leftI)
    apply simp by (metis args_nin_f args_not_res memory_lookup_def)

  have footQ2: "assertion_footprint_right (- {mk_variable_untyped args}) Q"
    apply (subst assertion_footprint_right_left)
    apply (rewrite at "assertion_footprint_left _ \<hole>" eq_reflection[of _ Q])
     close (unfold Q_def, metis)
    by (rule footQ1)

  show ?thesis
    apply (rule call_rule[where P=P and Q=Q])
    close 2 (rule globals_f)+
    close 2 (rule args_nin_f)+
    close (rule footQ1) close (rule footQ2)
    close (rule PfQ)
    using p1p2[unfolded C_def QB_def] by blast
qed



(* lemma callproc_split_args_result: 
  (* assumes fX: "set (vars_proc_global f) \<subseteq> X" *)
  (* assumes eX: "set (e_vars e) \<subseteq> X" *)
  (* assumes Y: "Y \<subseteq> X \<union> set (p_vars p)" *)
  (* assumes xX: "mk_variable_untyped x \<notin> X" *)
  shows "obs_eq X Y (callproc p f e) (seq (seq (assign (variable_pattern x) e) (callproc (variable_pattern y) f (var_expression x))) (assign p (var_expression y)))"
proof -
  have "obs_eq X Y (callproc p f e) 
    (seq (callproc (variable_pattern y) f e) (assign p (var_expression y)))"
    apply (rule callproc_split_result)
    sorry
  have "obs_eq X Y (callproc (variable_pattern y) f e) 
      (seq (assign (variable_pattern x) e) (callproc (variable_pattern y) f (var_expression x)))"
    apply (rule callproc_split_args)
qed    
 *)

(*
lemma call_rule_abstract_complex: 
  fixes res and globals_f and x1::"'x::prog_type pattern" and x2::"'x::prog_type pattern" 
    and y1::"'y::prog_type expression" and y2::"'y::prog_type expression" 
    and A B 
  assumes globals_f: "set(write_vars_proc_global f) \<subseteq> set globals_f"
  assumes globals_f': "set(vars_proc_global f) \<supseteq> set globals_f"
  assumes res_nin_f: "mk_variable_untyped res \<notin> set (vars_proc_global f)"
  assumes args_nin_f: "mk_variable_untyped args \<notin> set (vars_proc_global f)"
  assumes args_not_res: "mk_variable_untyped args \<noteq> mk_variable_untyped res"
  defines "P == \<lambda>m1 m2. \<forall>x\<in>set (vars_proc_global f) \<union> {mk_variable_untyped res, mk_variable_untyped args}.
                    memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  defines "P' == \<lambda>m1 m2. \<forall>x\<in>set (vars_proc_global f) \<union> {mk_variable_untyped res, mk_variable_untyped args}.
                    memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  defines "Q == \<lambda>m1 m2. \<forall>x\<in>set (vars_proc_global f) \<union> {mk_variable_untyped res}. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  defines "QB == (\<lambda>m1 m2. (\<forall>gL gR xL xR x'L x'R. 
                     Q (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) (list_pattern_untyped (p_vars x1)) x'L) res xL)
                       (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR) (list_pattern_untyped (p_vars x2)) x'R) res xR)
                \<longrightarrow> B (memory_update_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) x1 xL)
                      (memory_update_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR) x2 xR)))"
  defines "C == (\<lambda>m1 m2. P (memory_update m1 args (e_fun y1 m1)) (memory_update m2 args (e_fun y2 m2)) \<and> QB m1 m2)"
  defines "QB' == (\<lambda>m1 m2. (\<forall>gL gR xL xR x'L x'R. 
                     (Q (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) (list_pattern_untyped (p_vars x1)) x'L) res xL)
                       (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR) (list_pattern_untyped (p_vars x2)) x'R) res xR)
                      \<and> xL=xR) 
                \<longrightarrow> B (memory_update_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) x1 xL)
                      (memory_update_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR) x2 xR)))"
  defines "C' == (\<lambda>m1 m2. P' (memory_update m1 args (e_fun y1 m1)) (memory_update m2 args (e_fun y2 m2)) \<and> QB' m1 m2)"
  assumes p1p2': "rhoare A p1 p2 C'"
  shows "rhoare A (seq p1 (callproc x1 f y1)) (seq p2 (callproc x2 f y2)) B"
proof -
  (* fix res :: "'x variable" and args :: "'y variable" (* TODO *) *)

(*   def P == "\<lambda>m1 m2. \<forall>x\<in>set (vars_proc_global f) \<union> {mk_variable_untyped res, mk_variable_untyped args}.
                    memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  def Q == "\<lambda>m1 m2. \<forall>x\<in>set (vars_proc_global f) \<union> {mk_variable_untyped res}. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x" *)

  have aux: "(\<forall>x\<in>X. f x) = (\<forall>x\<in>X. g x)" if "\<And>x. x\<in>X \<Longrightarrow> f x = g x" for X::"variable_untyped set" and f g
    using that by blast

(* 
  defines "Q == \<lambda>m1 m2. \<forall>x\<in>set (vars_proc_global f) \<union> {mk_variable_untyped res}. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
*)
    
  (* {fix m1 m2 gL gR x'L x'R xL xR *)
  have "Q (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) (list_pattern_untyped (p_vars x1)) x'L) res xL)
          (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR) (list_pattern_untyped (p_vars x2)) x'R) res xR)
    \<Longrightarrow> x'L = x'R \<and> gL = gR \<and> xL = xR" 
    (* TODO: gL=gR only holds on vars outside x1/x2 *)
    for m1 m2 gL gR x'L x'R xL xR 
(*     unfolding Q_def by auto
  also have "?rhs \<Longrightarrow> Q (memory_update_untyped_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) (list_pattern_untyped (p_vars x1)) x'L)
          (memory_update_untyped_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR) (list_pattern_untyped (p_vars x2)) x'R)
        \<and> xL = xR"
    apply simp
    unfolding Q_def apply auto
        by auto *)
          
  hence QB'QB: "QB' m1 m2 \<Longrightarrow> QB m1 m2" for m1 m2
    unfolding QB'_def QB_def by metis

  have P'P: "P' m1 m2 \<Longrightarrow> P m1 m2" for m1 m2
    unfolding P'_def P_def by simp

  from QB'QB P'P have "C' m1 m2 \<Longrightarrow> C m1 m2" for m1 m2 unfolding C'_def C_def by simp
  hence p1p2: "rhoare A p1 p2 C"
    apply (rule_tac rconseq_rule[OF _ _ p1p2'])
    by auto

  have "obs_eq (set(vars_proc_global f) \<union> {mk_variable_untyped res, mk_variable_untyped args})  
      (set(vars_proc_global f) \<union> {mk_variable_untyped res}) 
      (callproc (variable_pattern res) f (var_expression args)) (callproc (variable_pattern res) f (var_expression args))"
    by (rule self_obseq_vars, auto)
  hence PfQ: "rhoare P (callproc (variable_pattern res) f (var_expression args))
                 (callproc (variable_pattern res) f (var_expression args)) Q"
    unfolding obs_eq_def P_def Q_def by simp

  have footQ1: "assertion_footprint_left (- {mk_variable_untyped args}) Q"
    unfolding Q_def
    apply (rule assertion_footprint_leftI)
    apply simp by (metis args_nin_f args_not_res memory_lookup_def)

  have footQ2: "assertion_footprint_right (- {mk_variable_untyped args}) Q"
    apply (subst assertion_footprint_right_left)
    apply (rewrite at "assertion_footprint_left _ \<hole>" eq_reflection[of _ Q])
     close (unfold Q_def, metis)
    by (rule footQ1)

  show ?thesis
    apply (rule call_rule[where P=P and Q=Q])
    close 2 (rule globals_f)+
    close 2 (rule args_nin_f)+
    close (rule footQ1) close (rule footQ2)
    close (rule PfQ)
    by (rule p1p2[unfolded C_def QB_def])
qed
*)

end