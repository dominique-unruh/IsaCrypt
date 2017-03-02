theory Callproc
imports RHL_Typed
begin

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
  define eq where "eq \<equiv> \<lambda>X m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
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


lemma callproc_split_result: 
  assumes footQ1: "assertion_footprint_left (-{mk_variable_untyped x1}) Q"
  assumes footQ2: "assertion_footprint_right (-{mk_variable_untyped x2}) Q"
  assumes rh: "rhoare P (seq (seq c1 (callproc (variable_pattern x1) f1 e1)) (assign p1 (var_expression x1)))
                        (seq (seq c2 (callproc (variable_pattern x2) f2 e2)) (assign p2 (var_expression x2))) Q"
  shows "rhoare P (seq c1 (callproc p1 f1 e1)) (seq c2 (callproc p2 f2 e2)) Q"
proof -
  let ?x1 = "mk_variable_untyped x1"
  let ?x2 = "mk_variable_untyped x2"
  define eq where "eq \<equiv> \<lambda>X m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
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
  defines "QB' == (\<lambda>m1 m2. (\<forall>g x. 
                B (memory_update (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) g) x1 x)
                  (memory_update (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) g) x2 x)))"
  defines "C' == (\<lambda>m1 m2. 
      (\<forall>x\<in>set (vars_proc_global f). memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)
    \<and> memory_lookup m1 y1 = memory_lookup m2 y2
    \<and> QB' m1 m2)"
  assumes p1p2': "rhoare A p1 p2 C'"
  shows "rhoare A (seq p1 (callproc (variable_pattern x1) f (var_expression y1))) 
                  (seq p2 (callproc (variable_pattern x2) f (var_expression y2))) B"
proof -
  define Q where "Q \<equiv> \<lambda>m1 m2. \<forall>x\<in>set (vars_proc_global f) \<union> {mk_variable_untyped res}. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  define QB where "QB \<equiv> \<lambda>m1 m2. (\<forall>gL gR xL xR x'L x'R. gL \<in> t_domain (pu_type (list_pattern_untyped globals_f)) \<longrightarrow>
                 gR \<in> t_domain (pu_type (list_pattern_untyped globals_f)) \<longrightarrow>
                     Q (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) (list_pattern_untyped (p_vars (variable_pattern x1))) x'L) res xL)
                       (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR) (list_pattern_untyped (p_vars (variable_pattern x2))) x'R) res xR)
                \<longrightarrow> B (memory_update_pattern
                     (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) (variable_pattern x1) xL)
                  (memory_update_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR)
                    (variable_pattern x2) xR))"
  define P where "P \<equiv> \<lambda>m1 m2. \<forall>x\<in>set (vars_proc_global f) \<union> {mk_variable_untyped args}.
                    memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
  define C where "C \<equiv> \<lambda>m1 m2. P (memory_update m1 args (e_fun (var_expression y1) m1))
              (memory_update m2 args (e_fun (var_expression y2) m2)) \<and> QB m1 m2"


  have Q': "gL = gR \<and> xL = xR" 
    if gL_type: "gL \<in> t_domain (pu_type (list_pattern_untyped globals_f))"
    and gR_type: "gR \<in> t_domain (pu_type (list_pattern_untyped globals_f))" 
    and Q: "Q (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m1 (list_pattern_untyped globals_f) gL) (list_pattern_untyped (p_vars (variable_pattern x1))) x'L) res xL)
           (memory_update (memory_update_untyped_pattern (memory_update_untyped_pattern m2 (list_pattern_untyped globals_f) gR) (list_pattern_untyped (p_vars (variable_pattern x2))) x'R) res xR)"
            (is "Q ?ml ?mr")
    for m1 m2 gL gR x'L x'R xL xR 
  proof -
    define ml where "ml \<equiv> ?ml"
    define mr where "mr \<equiv> ?mr"
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
        (* and "memory_lookup m1 res = memory_lookup m2 res" *) for m1 m2
    unfolding P_def using that by auto

  from QB'QB P'P have "C' m1 m2 \<Longrightarrow> C m1 m2" for m1 m2 unfolding C'_def C_def by simp
  hence p1p2: "rhoare A p1 p2 C"
    apply (rule_tac rconseq_rule[OF _ _ p1p2'])
    by auto

  have "obs_eq (set(vars_proc_global f) \<union> {mk_variable_untyped args})  
               (set(vars_proc_global f) \<union> {mk_variable_untyped res}) 
               (callproc (variable_pattern res) f (var_expression args))
               (callproc (variable_pattern res) f (var_expression args))"
    apply (rule self_obs_eq_callproc)
        unfolding vars_proc_global_def by auto
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




end