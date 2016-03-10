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

end