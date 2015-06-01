theory RHL_Untyped
imports Lang_Untyped Hoare_Untyped "~~/src/HOL/Library/Rewrite"
begin

definition rhoare_untyped :: "(memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> program_rep \<Rightarrow> program_rep \<Rightarrow> (memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "rhoare_untyped pre c1 c2 post =
  (\<forall>m1 m2. pre m1 m2 \<longrightarrow> 
     (\<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped c1 m1
        \<and> apply_to_distr snd \<mu> = denotation_untyped c2 m2
        \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> post m1' m2')))"

definition rhoare_denotation :: "(memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (memory \<Rightarrow> memory \<Rightarrow> bool) \<Rightarrow> bool" where
  "rhoare_denotation pre c1 c2 post =
  (\<forall>m1 m2. pre m1 m2 \<longrightarrow> 
     (\<exists>\<mu>. apply_to_distr fst \<mu> = c1 m1
        \<and> apply_to_distr snd \<mu> = c2 m2
        \<and> (\<forall>m1' m2'. (m1',m2') \<in> support_distr \<mu> \<longrightarrow> post m1' m2')))"

lemma rhoare_untyped_rhoare_denotation: "rhoare_untyped pre c1 c2 post = rhoare_denotation pre (denotation_untyped c1) (denotation_untyped c2) post"
  unfolding rhoare_untyped_def rhoare_denotation_def ..




lemma rskip_rule:
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> Q m1 m2"
  shows "rhoare_untyped P Skip Skip Q"
  unfolding rhoare_untyped_def apply (rule, rule, rule)
  apply (rule_tac x="point_distr (m1,m2)" in exI)
  using assms by simp

lemma rconseq_rule:
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> P' m1 m2"
      and "\<forall>m1 m2. Q' m1 m2 \<longrightarrow> Q m1 m2"
      and "rhoare_untyped P' c1 c2 Q'"
  shows "rhoare_untyped P c1 c2 Q"
  using assms unfolding rhoare_untyped_def by metis

lemma hoare_to_rhoare:
  assumes "lossless_untyped c"
      and h:"\<forall>m2. hoare_untyped (\<lambda>m1. P m1 m2) c (\<lambda>m1. Q m1 m2)"
  shows "rhoare_untyped P c Skip Q"
proof (unfold rhoare_untyped_def, rule, rule, rule)
  fix m1 m2 assume Pm1m2: "P m1 m2"
  def witness == "product_distr (denotation_untyped c m1) (denotation_untyped Skip m2)"
  show " \<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped c m1 \<and>
             apply_to_distr snd \<mu> = denotation_untyped Skip m2 \<and>
             (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
    apply (rule exI[where x=witness])
    unfolding witness_def apply auto
    apply (metis scaleR_one_distr)
    apply (metis `lossless_untyped c` lossless_untyped_def scaleR_one_distr)
    by (metis Pm1m2 h hoare_untyped_def)
qed

lemma cong_middle: "x = x' \<Longrightarrow> f x y = f x' y" by simp

lemma rsymmetric_rule:
  assumes "rhoare_untyped (\<lambda>m1 m2. P m2 m1) c2 c1 (\<lambda>m1 m2. Q m2 m1)"
  shows "rhoare_untyped P c1 c2 Q"
proof (unfold rhoare_untyped_def, rule, rule, rule)
  fix m1 m2 assume P: "P m1 m2"
  obtain witness where wit2: "apply_to_distr fst witness = denotation_untyped c2 m2"
                   and wit1: "apply_to_distr snd witness = denotation_untyped c1 m1"
                   and correct: "\<forall>m1' m2'. (m1', m2') \<in> support_distr witness \<longrightarrow> Q m2' m1'"
       by (metis (mono_tags) P assms rhoare_untyped_def)
  def witness' == "apply_to_distr (\<lambda>(x,y). (y,x)) witness"
  have wit'1: "apply_to_distr fst witness' = denotation_untyped c1 m1"
    unfolding witness'_def wit1[symmetric] apply auto
    apply (rule cong_middle[where f=apply_to_distr])
    by auto
  have wit'2: "apply_to_distr snd witness' = denotation_untyped c2 m2"
    unfolding witness'_def wit2[symmetric] apply auto
    apply (rule cong_middle[where f=apply_to_distr])
    by auto
  also have correct': "\<forall>m1 m2. (m1, m2) \<in> support_distr witness' \<longrightarrow> Q m1 m2"
    unfolding witness'_def using correct by auto

  show "\<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped c1 m1 \<and>
                  apply_to_distr snd \<mu> = denotation_untyped c2 m2 \<and> (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
    using wit'1 wit'2 correct' by auto            
qed

lemma rassign_rule1:
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> Q (memory_update_untyped m1 x (eu_fun e m1)) m2"
  shows "rhoare_untyped P (Assign x e) Skip Q"
  apply (rule hoare_to_rhoare)
  unfolding lossless_untyped_def apply simp
  apply (rule allI, rule assign_rule)
  using assms by simp

lemma rassign_rule2:
  assumes "\<forall>m1 m2. P m1 m2 \<longrightarrow> Q m1 (memory_update_untyped m2 x (eu_fun e m2))"
  shows "rhoare_untyped P Skip (Assign x e) Q"
apply (rule rsymmetric_rule)
apply (rule rassign_rule1)
using assms by simp

(*
lemma rnd_rule:
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>y\<in>support_distr (ed_fun e m2). y = f (f' y)"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>x\<in>support_distr (ed_fun d m1). x = f' (f x)"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>y\<in>support_distr (ed_fun e m2). prob (ed_fun e m2) y = prob (ed_fun d m1) (f' y)"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>x\<in>support_distr (ed_fun d m1). f x \<in> support_distr (ed_fun e m2)"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>x\<in>support_distr (ed_fun d m1). Q (memory_update_untyped m1 x) (memory_update_untyped m2 (f x))"
  shows "rhoare_untyped P (Sample x d) (Sample y e) Q"
*)

lemma rnd_rule:
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> apply_to_distr fst (\<mu> m1 m2) = ed_fun d m1"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> apply_to_distr snd (\<mu> m1 m2) = ed_fun e m2"
      and "\<And>m1 m2. P m1 m2 \<Longrightarrow> \<forall>(xval,yval)\<in>support_distr (\<mu> m1 m2). Q (memory_update_untyped m1 x xval) (memory_update_untyped m2 y yval)"
  shows "rhoare_untyped P (Sample x d) (Sample y e) Q"
  unfolding rhoare_untyped_def apply rule+ defer apply rule
proof -
  fix m1 m2 assume "P m1 m2"
  def map == "\<lambda>(xval,yval). (memory_update_untyped m1 x xval, memory_update_untyped m2 y yval)"
  def \<mu>' == "apply_to_distr map (\<mu> m1 m2)"
  have mu1: "apply_to_distr fst (\<mu> m1 m2) = ed_fun d m1" using assms `P m1 m2` by simp
  have mu2: "apply_to_distr snd (\<mu> m1 m2) = ed_fun e m2" using assms `P m1 m2` by simp
  have post: "\<forall>(xval,yval)\<in>support_distr (\<mu> m1 m2). Q (memory_update_untyped m1 x xval) (memory_update_untyped m2 y yval)"
    using assms `P m1 m2` by simp
  show "apply_to_distr fst \<mu>' = denotation_untyped (Sample x d) m1"
    unfolding \<mu>'_def apply simp
    unfolding mu1[symmetric] apply simp
    apply (rule cong_middle[where f=apply_to_distr])
    unfolding map_def by auto
  show "apply_to_distr snd \<mu>' = denotation_untyped (Sample y e) m2" 
    unfolding \<mu>'_def apply simp
    unfolding mu2[symmetric] apply simp
    apply (rule cong_middle[where f=apply_to_distr])
    unfolding map_def by auto
  show "\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu>' \<longrightarrow> Q m1' m2'" 
    unfolding \<mu>'_def map_def using post by auto
qed


lemma rtrans_rule:
  assumes p:"\<And>m1 m2. P m1 m2 \<Longrightarrow> \<exists>m. P1 m1 m \<and> P2 m m2"
      and q:"\<And>m1 m2 m. Q1 m1 m \<Longrightarrow> Q2 m m2 \<Longrightarrow> Q m1 m2"
      and rhl1: "rhoare_untyped P1 c1 c Q1"
      and rhl2: "rhoare_untyped P2 c c2 Q2"
  shows "rhoare_untyped P c1 c2 Q"
proof (unfold rhoare_untyped_def, auto (*, rule exI, auto*))
  fix m1 m2 assume "P m1 m2"
  then obtain m where "P1 m1 m" and "P2 m m2" using p by metis
  obtain \<mu>1 where \<mu>1fst: "apply_to_distr fst \<mu>1 = denotation_untyped c1 m1"
              and \<mu>1snd: "apply_to_distr snd \<mu>1 = denotation_untyped c m"
              and \<mu>1supp: "\<And>m1' m'. (m1',m') \<in> support_distr \<mu>1 \<Longrightarrow> Q1 m1' m'"
    using `P1 m1 m` rhl1 unfolding rhoare_untyped_def by metis
  obtain \<mu>2 where \<mu>2fst: "apply_to_distr fst \<mu>2 = denotation_untyped c m"
              and \<mu>2snd: "apply_to_distr snd \<mu>2 = denotation_untyped c2 m2"
              and \<mu>2supp: "\<And>m' m2'. (m',m2') \<in> support_distr \<mu>2 \<Longrightarrow> Q2 m' m2'"
    using `P2 m m2` rhl2 unfolding rhoare_untyped_def by metis
  obtain \<mu>3 where \<mu>31: "apply_to_distr (\<lambda>(x,y,z). (x,y)) \<mu>3 = \<mu>1" 
              and \<mu>32: "apply_to_distr (\<lambda>(x,y,z). (y,z)) \<mu>3 = \<mu>2"
    using markov_chain \<mu>1snd \<mu>2fst by metis
  def \<mu> == "apply_to_distr (\<lambda>(x,y,z). (x,z)) \<mu>3"
  show "\<exists>\<mu>. apply_to_distr fst \<mu> = denotation_untyped c1 m1 \<and>
            apply_to_distr snd \<mu> = denotation_untyped c2 m2 \<and> 
            (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu> \<longrightarrow> Q m1' m2')"
  proof (rule exI, auto)
    have tmp: "(\<lambda>x. fst (case x of (x, y, xb) \<Rightarrow> (x, xb))) = (\<lambda>(x,y,z). x)" by auto 
    show "apply_to_distr fst \<mu> = denotation_untyped c1 m1"
      unfolding \<mu>_def \<mu>1fst[symmetric] \<mu>31[symmetric] apply simp 
      by (rule cong_middle[where f=apply_to_distr], auto)
    show "apply_to_distr snd \<mu> = denotation_untyped c2 m2"
      unfolding \<mu>_def \<mu>2snd[symmetric] \<mu>32[symmetric] apply simp 
      by (rule cong_middle[where f=apply_to_distr], auto)
    fix m1' m2' assume in\<mu>: "(m1', m2') \<in> support_distr \<mu>"
    show "Q m1' m2'"
    proof -
      obtain m' where \<mu>3supp: "(m1',m',m2') \<in> support_distr \<mu>3"
        using in\<mu> unfolding \<mu>_def by auto
      from \<mu>3supp have in\<mu>1supp: "(m1',m') \<in> support_distr \<mu>1"
        unfolding \<mu>31[symmetric] by force
      from \<mu>3supp have in\<mu>2supp: "(m',m2') \<in> support_distr \<mu>2"
        unfolding \<mu>32[symmetric] by force
      show "Q m1' m2'"
        by (metis \<mu>1supp \<mu>2supp in\<mu>1supp in\<mu>2supp q)
    qed
  qed
qed

lemma rcase_rule:
  assumes "\<And>x. rhoare_untyped (\<lambda>m1 m2. P m1 m2 \<and> f m1 m2 = x) c1 c2 Q"
  shows "rhoare_untyped P c1 c2 Q"
using assms unfolding rhoare_untyped_def by metis


lemma rseq_rule_denotation: 
  assumes PcQ: "rhoare_denotation P c1 c2 Q"
  assumes QcR: "rhoare_denotation Q c1' c2' R"
  shows "rhoare_denotation P (\<lambda>m. compose_distr c1' (c1 m)) (\<lambda>m. compose_distr c2' (c2 m)) R"
proof (unfold rhoare_denotation_def, rule, rule, rule)
  fix m1 m2 assume "P m1 m2"
  with PcQ obtain \<mu> 
    where fst\<mu>: "apply_to_distr fst \<mu> = c1 m1"
    and   snd\<mu>: "apply_to_distr snd \<mu> = c2 m2"
    and   \<mu>supp: "(\<forall>(m1', m2') \<in> support_distr \<mu>. Q m1' m2')" 
      unfolding rhoare_denotation_def apply atomize_elim by blast
  obtain \<mu>0 where \<mu>0: "\<forall>m1 m2. (m1,m2)\<in>support_distr \<mu> \<longrightarrow>
          (apply_to_distr fst (\<mu>0 m1 m2) = c1' m1 \<and>
           apply_to_distr snd (\<mu>0 m1 m2) = c2' m2 \<and> 
          (\<forall>m1' m2'. (m1', m2') \<in> support_distr (\<mu>0 m1 m2) \<longrightarrow> R m1' m2'))"
    apply (atomize_elim) apply (rule choice, rule allI, rule choice, rule allI, simp)
    using QcR unfolding rhoare_denotation_def using \<mu>supp by auto
  def \<mu>' == "\<lambda>(m1,m2). \<mu>0 m1 m2"
  def \<mu>'' == "compose_distr \<mu>' \<mu>"
  have "\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu>'' \<longrightarrow> R m1' m2'"
    apply auto unfolding \<mu>''_def Distr.support_compose_distr
    using \<mu>'_def \<mu>0 by auto
  moreover have "apply_to_distr fst \<mu>'' = compose_distr c1' (c1 m1)"
    unfolding \<mu>''_def
    unfolding Distr.compose_point_distr_l[symmetric] Distr.compose_distr_assoc[symmetric]
    unfolding Distr.compose_point_distr_l
    apply (subst compose_distr_cong[of \<mu> _ "\<lambda>(m1,m2). c1' m1"])
    close (simp add: \<mu>'_def \<mu>0 case_prod_unfold)  
    unfolding fst\<mu>[symmetric] compose_distr_apply_to_distr o_def
    by (meson case_prod_unfold)
  moreover have "apply_to_distr snd \<mu>'' = compose_distr c2' (c2 m2)"
    unfolding \<mu>''_def 
    unfolding Distr.compose_point_distr_l[symmetric] Distr.compose_distr_assoc[symmetric]
    unfolding Distr.compose_point_distr_l
    apply (subst compose_distr_cong[of \<mu> _ "\<lambda>(m1,m2). c2' m2"])
    close (simp add: \<mu>'_def \<mu>0 case_prod_unfold)  
    unfolding snd\<mu>[symmetric] compose_distr_apply_to_distr o_def
    by (meson case_prod_unfold)
  ultimately
  show "\<exists>\<mu>''. apply_to_distr fst \<mu>'' = compose_distr c1' (c1 m1) \<and>
              apply_to_distr snd \<mu>'' = compose_distr c2' (c2 m2) \<and>
              (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu>'' \<longrightarrow> R m1' m2')"
    by auto
qed


lemma rseq_rule: 
  assumes PcQ: "rhoare_untyped P c1 c2 Q"
  assumes QcR: "rhoare_untyped Q c1' c2' R"
  shows "rhoare_untyped P (Seq c1 c1') (Seq c2 c2') R"
using assms unfolding rhoare_untyped_rhoare_denotation denotation_untyped_Seq[THEN ext]
by (rule rseq_rule_denotation)
(*
proof (unfold rhoare_untyped_def, rule, rule, rule)
  fix m1 m2 assume "P m1 m2"
  with PcQ obtain \<mu> 
    where fst\<mu>: "apply_to_distr fst \<mu> = denotation_untyped c1 m1"
    and   snd\<mu>: "apply_to_distr snd \<mu> = denotation_untyped c2 m2"
    and   \<mu>supp: "(\<forall>(m1', m2') \<in> support_distr \<mu>. Q m1' m2')" 
      unfolding rhoare_untyped_def apply atomize_elim by blast
  obtain \<mu>0 where \<mu>0: "\<forall>m1 m2. (m1,m2)\<in>support_distr \<mu> \<longrightarrow>
          (apply_to_distr fst (\<mu>0 m1 m2) = denotation_untyped c1' m1 \<and>
           apply_to_distr snd (\<mu>0 m1 m2) = denotation_untyped c2' m2 \<and> 
          (\<forall>m1' m2'. (m1', m2') \<in> support_distr (\<mu>0 m1 m2) \<longrightarrow> R m1' m2'))"
    apply (atomize_elim) apply (rule choice, rule allI, rule choice, rule allI, simp)
    using QcR unfolding rhoare_untyped_def using \<mu>supp by auto
  def \<mu>' == "\<lambda>(m1,m2). \<mu>0 m1 m2"
  def \<mu>'' == "compose_distr \<mu>' \<mu>"
  have "\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu>'' \<longrightarrow> R m1' m2'"
    apply auto unfolding \<mu>''_def Distr.support_compose_distr
    using \<mu>'_def \<mu>0 by auto
  moreover have "apply_to_distr fst \<mu>'' = denotation_untyped (Seq c1 c1') m1"
    unfolding \<mu>''_def apply simp 
    unfolding Distr.compose_point_distr_l[symmetric] Distr.compose_distr_assoc[symmetric]
    unfolding Distr.compose_point_distr_l
    apply (subst compose_distr_cong[of \<mu> _ "\<lambda>(m1,m2). denotation_untyped c1' m1"])
    close (simp add: \<mu>'_def \<mu>0 case_prod_unfold)  
    unfolding fst\<mu>[symmetric] compose_distr_apply_to_distr o_def
    by (meson case_prod_unfold)
  moreover have "apply_to_distr snd \<mu>'' = denotation_untyped (Seq c2 c2') m2"
    unfolding \<mu>''_def apply simp 
    unfolding Distr.compose_point_distr_l[symmetric] Distr.compose_distr_assoc[symmetric]
    unfolding Distr.compose_point_distr_l
    apply (subst compose_distr_cong[of \<mu> _ "\<lambda>(m1,m2). denotation_untyped c2' m2"])
    close (simp add: \<mu>'_def \<mu>0 case_prod_unfold)  
    unfolding snd\<mu>[symmetric] compose_distr_apply_to_distr o_def
    by (meson case_prod_unfold)
  ultimately
  show "\<exists>\<mu>''. apply_to_distr fst \<mu>'' = denotation_untyped (Seq c1 c1') m1 \<and>
              apply_to_distr snd \<mu>'' = denotation_untyped (Seq c2 c2') m2 \<and>
              (\<forall>m1' m2'. (m1', m2') \<in> support_distr \<mu>'' \<longrightarrow> R m1' m2')"
    by auto
qed
*)



(*definition "blockassign (xs::variable_untyped list) (es::expression_untyped list) == 
  fold (\<lambda>(x,e) p. Seq p (Assign x e)) (zip xs es) Skip"*)

definition "obs_eq_untyped X Y c1 c2 ==
  rhoare_untyped (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)
                 c1 c2
                 (\<lambda>m1 m2. \<forall>x\<in>Y. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"

lemma rhoare_denotation_post_eq: 
  fixes X c1 c2 P
  defines "project == (\<lambda>m x. if x\<in>X then memory_lookup_untyped m x else undefined)"
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> apply_to_distr project (c1 m1) = apply_to_distr project (c2 m2)"
  shows "rhoare_denotation P c1 c2 (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
SORRY

lemma rhoare_denotation_post_eq2: 
  fixes X c1 c2 P
  defines "project == (\<lambda>m x. if x\<in>X then memory_lookup_untyped m x else undefined)"
  assumes "rhoare_denotation P c1 c2 (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
  shows "\<And>m1 m2. P m1 m2 \<Longrightarrow> apply_to_distr project (c1 m1) = apply_to_distr project (c2 m2)"
SORRY

(*
lemma obs_eq_untypedI: 
  fixes X c1 c2
  defines "project == (\<lambda>m x. if x\<in>X then memory_lookup_untyped m x else undefined)"
  assumes "\<And>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x
            \<Longrightarrow> apply_to_distr project (denotation_untyped c1 m1)
              = apply_to_distr project (denotation_untyped c2 m2)"
  shows "obs_eq_untyped X c1 c2"
unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation
apply (rule rhoare_denotation_post_eq)
using assms by auto
*)

lemma obs_eq_untyped_sym: 
  assumes "obs_eq_untyped X Y c d"
  shows "obs_eq_untyped X Y d c"
SORRY


lemma self_obseq_vars:
  assumes "set(vars_untyped c) \<subseteq> X"
  assumes "Y \<subseteq> X"
  shows "obs_eq_untyped X Y c c"
SORRY

lemma self_obseq_assign:
  assumes "set (eu_vars e) \<subseteq> X"
  assumes "Y \<subseteq> X\<union>{x}"
  shows "obs_eq_untyped X Y (Assign x e) (Assign x e)"
SORRY


definition "assign_local_vars (locals::variable_untyped list) vs es = 
  fold (\<lambda>(x,e) p. Seq p (Assign x e)) (zip vs es)
  (fold (\<lambda>x p. Seq p (Assign x (const_expression_untyped (vu_type x) (t_default (vu_type x))))) 
  locals Skip)"


lemma well_typed_assign_local_vars:
  assumes "map vu_type vs = map eu_type es"
  shows "well_typed (assign_local_vars locals vs es)"
proof -
  have wt_nil: "well_typed (assign_local_vars locals [] [])"
    apply (induction locals rule:rev_induct)
    by (auto simp: assign_local_vars_def eu_type_const_expression_untyped)
  have nest: "assign_local_vars locals vs es = 
        fold (\<lambda>(x, e) p. Seq p (Assign x e)) (zip vs es) (assign_local_vars locals [] [])"
    unfolding assign_local_vars_def by auto
  def zip_vs_es == "zip vs es"
  have vs_es_type: "\<forall>(v,e)\<in>set zip_vs_es. eu_type e = vu_type v"
    using assms[unfolded list_eq_iff_zip_eq] unfolding zip_vs_es_def zip_map_map by auto
  show "well_typed (assign_local_vars locals vs es)"
    unfolding nest zip_vs_es_def[symmetric]
    apply (insert vs_es_type)
    apply (induction zip_vs_es rule:rev_induct) 
    using wt_nil by auto
qed

lemma fold_commute: 
  assumes "\<And>x y. f (g x y) = g' x (f y)"
  shows "f (fold g l a) = fold g' l (f a)"
    apply (induction l arbitrary: a)
    using assms by auto

lemma fold_o: 
  shows "(fold (\<lambda>x. op o (f x)) l a) m = fold f l (a m)"
  by (induction l arbitrary: a, auto)

lemma zip_hd: 
  assumes "(a, b) # x = zip as bs"
  shows "as = a#tl as" and "bs = b#tl bs"
apply (insert assms)
apply (induction bs, auto)
apply (metis list.exhaust list.sel(1) list.sel(3) prod.sel(1) zip_Cons_Cons zip_Nil)
apply (induction bs arbitrary: as, auto)
by (metis Pair_inject list.distinct(2) list.exhaust list.inject zip_Cons_Cons zip_Nil)


lemma inline_rule:
  fixes body pargs ret x args V locals
  defines "p == Proc body pargs ret"
  assumes body_locals: "\<And>x. \<lbrakk> x\<in>set(vars_untyped body); \<not> vu_global x \<rbrakk> \<Longrightarrow> x\<in>set locals"
  assumes pargs_locals: "\<And>x. x\<in>set pargs \<Longrightarrow> x\<in>set locals"
  assumes ret_locals: "\<And>x. \<lbrakk> x\<in>set(eu_vars ret); \<not> vu_global x \<rbrakk> \<Longrightarrow> x\<in>set locals"
  assumes locals_local: "\<And>x. x\<in>set locals \<Longrightarrow> \<not> vu_global x"
  assumes argvars_locals: "\<And>e x. e\<in>set args \<Longrightarrow> x\<in>set(eu_vars e) \<Longrightarrow> x\<notin>set locals"
  assumes localsV: "V \<inter> set locals \<subseteq> {x}"
  assumes globalsVbody: "\<And>x. x\<in>set(vars_untyped body) \<Longrightarrow> vu_global x \<Longrightarrow> x\<in>V"
  assumes globalsVret: "\<And>x. x\<in>set(eu_vars ret) \<Longrightarrow> vu_global x \<Longrightarrow> x\<in>V"
  assumes argvarsV: "\<And>e x. e\<in>set args \<Longrightarrow> set(eu_vars e) \<subseteq> V"
  defines "unfolded == Seq (Seq (assign_local_vars locals pargs args) body) (Assign x ret)"
  shows "obs_eq_untyped V V (CallProc x p args) unfolded"
proof -
  def eq == "\<lambda>V \<mu> \<nu>. apply_to_distr (\<lambda>m x. if x \<in> V then memory_lookup_untyped m x else undefined) \<mu>
                   = apply_to_distr (\<lambda>m x. if x \<in> V then memory_lookup_untyped m x else undefined) \<nu>"
  def eq == "\<lambda>X c1 c2. rhoare_denotation (\<lambda>m1 m2. \<forall>x\<in>V. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)
                                         c1 c2
                                         (\<lambda>m1 m2. \<forall>x\<in>X. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x)"
  have eq_mono: "\<And>A B c1 c2. A \<subseteq> B \<Longrightarrow> eq B c1 c2 \<Longrightarrow> eq A c1 c2"
    unfolding eq_def rhoare_denotation_def by blast

  def argvars == "set [x. e<-args, x<-eu_vars e]"

  def untouched == "\<lambda>V \<mu>. \<forall>m0. \<forall>m\<in>support_distr (\<mu> m0). \<forall>x\<in>V. memory_lookup_untyped m x = memory_lookup_untyped m0 x"
  def G == "{x\<in>V. vu_global x} :: variable_untyped set"
  have pargs_locals: "set pargs \<subseteq> set locals" 
    using pargs_locals by auto
  def co_locals == "{x. \<not>vu_global x \<and> x\<notin>set locals \<and> x\<notin>set pargs}"
  with pargs_locals have co_locals_def': "co_locals = {x. \<not>vu_global x \<and> x\<notin>set locals}"
    by auto


  def cp1 == "\<lambda>m1. point_distr (init_locals pargs args m1)" 
  def uf1 == "\<lambda>m2. denotation_untyped (assign_local_vars locals pargs args) m2"

  
  have uf1: "\<And>m2. uf1 m2 = point_distr
     (fold (\<lambda>(e,x) y. memory_update_untyped y e (eu_fun x y)) (zip pargs args)
       (fold (\<lambda>x y. memory_update_untyped y x (t_default (vu_type x))) locals m2))"
    unfolding eq_def uf1_def cp1_def assign_local_vars_def
    apply (subst fold_commute[where f=denotation_untyped 
                and g'="\<lambda>xe d. apply_to_distr (\<lambda>m::memory. memory_update_untyped m (fst xe) (eu_fun (snd xe) m)) o d"])
    close (case_tac x, simp add: denotation_untyped_Seq[THEN ext] denotation_untyped_Assign[THEN ext], auto)
    apply (subst fold_commute[where f=denotation_untyped 
                and g'="\<lambda>x d. apply_to_distr (\<lambda>m::memory. memory_update_untyped m x (t_default (vu_type x))) o d"])
    apply (simp add: denotation_untyped_Seq[THEN ext] denotation_untyped_Assign[THEN ext] o_def eu_fun_const_expression_untyped)
    apply (subst fold_o, subst fold_o, auto)
    apply (subst fold_commute[symmetric, where f=point_distr], simp)
    apply (subst fold_commute[symmetric, where f=point_distr], simp)
    unfolding apply_to_point_distr by (simp add: split_beta') 

  have eq1: "eq (G\<union>set locals) cp1 uf1"
  proof (unfold eq_def, rule rhoare_denotation_post_eq)
    fix m1 m2
    assume init_eqV: "\<forall>x\<in>V. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"

    def inner_right == "fold (\<lambda>x y. memory_update_untyped y x (t_default (vu_type x))) locals m2"
    def inner_left == "(Abs_memory (Rep_memory m1\<lparr>mem_locals := \<lambda>v. t_default (vu_type v)\<rparr>))"
    (* Does not hold for x\<in>argvars: inner_left might initialize those to t_default *)
    have inner_eq: "\<And>x. x\<in>G\<union>set locals \<Longrightarrow> memory_lookup_untyped inner_right x = memory_lookup_untyped inner_left x"
    proof (case_tac "x\<in>set locals")
      fix x assume "x\<in>set locals"
      hence "\<not>vu_global x" using locals_local by auto
      have "memory_lookup_untyped inner_right x
          = (if x\<in>set locals then t_default (vu_type x) else memory_lookup_untyped m2 x)"
        unfolding inner_right_def apply (induction locals arbitrary: m2) close auto
        apply auto
          close (simp add: memory_lookup_update_notsame_untyped)
          using Rep_type memory_lookup_update_same_untyped t_default_def t_domain_def close auto
          by (simp add: memory_lookup_update_notsame_untyped)
      with `x\<in>set locals` 
      have "memory_lookup_untyped inner_right x
          = t_default (vu_type x)" by simp
      also have "\<dots> = memory_lookup_untyped inner_left x"
        unfolding memory_lookup_untyped_def inner_left_def apply (simp add: `\<not>vu_global x`)
        apply (subst Abs_memory_inverse, auto)
        using Rep_memory by blast
      finally show "?thesis x" .
    next
      fix x assume "x\<notin>set locals" and "x\<in>G\<union>set locals"
      hence "x\<in>G" by simp
      have "vu_global x" using G_def `x \<in> G` by blast
      have "memory_lookup_untyped inner_right x
          = memory_lookup_untyped m2 x"
        unfolding inner_right_def
        apply (insert `x\<notin>set locals`)
        apply (induction locals arbitrary: m2, auto)
        by (subst memory_lookup_update_notsame_untyped, auto)
      also have "\<dots> = memory_lookup_untyped m1 x"
        using init_eqV G_def `x \<in> G` by auto 
      also have "\<dots> = memory_lookup_untyped inner_left x"
        unfolding inner_left_def memory_lookup_untyped_def apply (simp add: `vu_global x`)
        apply (subst Abs_memory_inverse, auto)
        using Rep_memory by blast
      finally show "?thesis x".
    qed

    have init_equal: "(\<lambda>x. if x \<in> G \<or> x \<in> set locals then memory_lookup_untyped (init_locals pargs args m1) x else undefined) =
               (\<lambda>x. if x \<in> G \<or> x \<in> set locals then memory_lookup_untyped
                    (fold (\<lambda>(e,x) y. memory_update_untyped y e (eu_fun x y)) (zip pargs args)
                    (fold (\<lambda>x y. memory_update_untyped y x (t_default (vu_type x))) locals m2))
                    x else undefined)"
    proof -
      def zip_pa == "zip pargs args"
      def upd == "(\<lambda>(e, x) y. memory_update_untyped y e (eu_fun x y))"
      def upd' == "(\<lambda>(e, x) y. memory_update_untyped y e (eu_fun x m1))"
      have argvars: "\<forall>pa\<in>set zip_pa. set(eu_vars(snd pa))\<subseteq>argvars \<and> fst pa\<notin>argvars" 
        unfolding zip_pa_def apply (rule ballI, case_tac pa, hypsubst, simp)
        apply (frule set_zip_rightD)
        apply (drule set_zip_leftD) 
        apply (rule conjI)
         close (auto simp: argvars_def)
        using argvars_locals argvars_def pargs_locals by auto
      have right_m1: "\<And>x. x\<in>argvars \<Longrightarrow> memory_lookup_untyped inner_right x = memory_lookup_untyped m1 x"
      proof - 
        fix x assume "x\<in>argvars"
        hence m1m2: "memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
          using argvarsV argvars_def init_eqV by auto
        have x_nin_locals: "x\<notin>set locals"
          using `x \<in> argvars` argvars_def argvars_locals by fastforce
        show "memory_lookup_untyped inner_right x = memory_lookup_untyped m1 x"
        proof (unfold inner_right_def, insert m1m2, insert x_nin_locals, induction locals arbitrary: m1 m2 rule:rev_induct)
        case Nil thus ?case by auto
        next case (snoc loc locals) 
          have x_nin_locals: "x\<notin>set locals"
            using snoc.prems by auto
          have IH: "memory_lookup_untyped (fold (\<lambda>x y. memory_update_untyped y x (t_default (vu_type x))) locals m2) x 
              = memory_lookup_untyped m1 x" 
            by (rule snoc.IH, fact snoc.prems, fact x_nin_locals)
          have "x\<noteq>loc"
            using snoc.prems by auto
          show ?case apply simp
            using IH `x \<noteq> loc` memory_lookup_update_notsame_untyped by auto
        qed
      qed
      have goal: "\<And>x. x \<in> G \<or> x \<in> set locals \<Longrightarrow> 
         memory_lookup_untyped (fold upd' zip_pa inner_left) x = memory_lookup_untyped (fold upd zip_pa inner_right) x
              \<and> (\<forall>y\<in>argvars. memory_lookup_untyped (fold upd zip_pa inner_right) y = memory_lookup_untyped m1 y)"
        apply (insert argvars)
        proof (induction zip_pa rule:rev_induct)
        case Nil thus ?case unfolding upd_def upd'_def using inner_eq right_m1 by auto
        next case (snoc pa zip_pa) 
          obtain p a where pa:"pa=(p,a)" by (cases pa, auto)
          have zip_pa: "\<forall>pa\<in>set zip_pa. set (eu_vars (snd pa)) \<subseteq> argvars \<and> fst pa \<notin> argvars"
            by (simp add: snoc.prems)
          def inner_right' == "fold upd zip_pa inner_right"
          def inner_left' == "fold upd' zip_pa inner_left"
          have inner_m1': "\<And>y. y\<in>argvars \<Longrightarrow> memory_lookup_untyped inner_right' y = memory_lookup_untyped m1 y"
            using snoc.IH snoc.prems zip_pa inner_right'_def by blast
          have inner_m1: "\<And>y. y\<in>argvars \<Longrightarrow> memory_lookup_untyped (fold upd (zip_pa @ [pa]) inner_right) y = memory_lookup_untyped m1 y"
            apply simp unfolding inner_right'_def[symmetric]
            unfolding upd_def pa apply simp
            apply (subst memory_lookup_update_notsame_untyped)
            using pa snoc.prems close auto
            using inner_m1' snoc.prems by blast
          have eval_eq: "eu_fun a m1 = eu_fun a inner_right'"
            apply (rule eu_fun_footprint)
            using inner_m1' pa snoc.prems by auto
          have same: "memory_lookup_untyped (fold upd' (zip_pa @ [pa]) inner_left) x
                    = memory_lookup_untyped (fold upd (zip_pa @ [pa]) inner_right) x"
            apply simp unfolding inner_right'_def[symmetric] inner_left'_def[symmetric]
            unfolding upd_def upd'_def pa apply simp unfolding eval_eq
            unfolding memory_lookup_update_untyped
            apply auto
            using inner_left'_def inner_right'_def snoc.IH snoc.prems(1) zip_pa by blast
          show ?case apply simp using inner_m1 same by auto 
      qed
      show ?thesis 
        unfolding init_locals_def inner_right_def[symmetric] inner_left_def[symmetric] Let_def zip_map2 fold_map 
        apply (rewrite at "fold \<hole>" to "upd'" eq_reflection)
         close (unfold upd'_def o_def split_beta', simp)
        unfolding upd_def[symmetric] zip_pa_def[symmetric]
        using goal by auto
    qed


    show "apply_to_distr (\<lambda>m x. if x \<in> G \<union> set locals then memory_lookup_untyped m x else undefined) (cp1 m1) =
          apply_to_distr (\<lambda>m x. if x \<in> G \<union> set locals then memory_lookup_untyped m x else undefined) (uf1 m2)"
      unfolding cp1_def uf1 apply_to_point_distr using init_equal by auto
  qed

  have untouched1: "untouched co_locals uf1"
    unfolding uf1 untouched_def co_locals_def proof auto
    fix m0 x assume "x\<notin>set pargs" assume "x\<notin>set locals"
    show "memory_lookup_untyped
          (fold (\<lambda>(e, x) y. memory_update_untyped y e (eu_fun x y)) (zip pargs args)
          (fold (\<lambda>x y. memory_update_untyped y x (t_default (vu_type x))) locals m0))
          x = memory_lookup_untyped m0 x"
    proof (insert `x\<notin>set locals`, induction locals arbitrary: m0)
    case Nil thus ?case
      apply simp
      apply (insert `x\<notin>set pargs`, induction "zip pargs args" arbitrary: pargs args m0)
      apply auto
      by (smt fold_simps(2) insertCI list.sel(3) list.simps(15) memory_lookup_update_notsame_untyped prod.sel(1) split_beta' zip_Cons_Cons zip_hd(1) zip_hd(2))
    next case (Cons l locals) thus ?case
      using memory_lookup_update_notsame_untyped by auto
    qed
  qed

  def uf2 == "\<lambda>m. compose_distr (denotation_untyped body) (uf1 m)"
  def cp2 == "\<lambda>m. compose_distr (denotation_untyped body) (cp1 m)"

  have eq_body: "obs_eq_untyped (G\<union>set locals) (G\<union>set locals) body body"
    apply (rule self_obseq_vars, rule, case_tac "x\<in>G", simp)
    apply auto using globalsVbody body_locals unfolding  G_def by auto

  have eq2: "eq (G\<union>set locals) cp2 uf2"
    unfolding eq_def uf2_def cp2_def
    apply (rule rseq_rule_denotation)
      close (fact eq1[unfolded eq_def])
      using eq_body unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation .
  have untouched2: "untouched co_locals uf2"
  proof (unfold untouched_def uf2_def, auto)
    fix m0 m' m x
    assume "m' \<in> support_distr (uf1 m0)" and x_co: "x \<in> co_locals"
    hence m'_m0: "memory_lookup_untyped m' x = memory_lookup_untyped m0 x"
      using untouched1 unfolding untouched_def by auto
    assume m: "m \<in> support_distr (denotation_untyped body m')"
    have x: "x \<notin> set(vars_untyped body)"
      using x_co body_locals unfolding co_locals_def by auto
    have m_m': "memory_lookup_untyped m x = memory_lookup_untyped m' x"
      apply (rule readonly_notin_vars[unfolded hoare_untyped_def, rule_format, where c=body and m=m'])
      using m x by auto
    with m'_m0 show "memory_lookup_untyped m x = memory_lookup_untyped m0 x" by simp
  qed

  def uf3 == "\<lambda>m. compose_distr (denotation_untyped (Assign x ret)) (uf2 m)"
  def cp3 == "\<lambda>m. compose_distr (denotation_untyped (Assign x ret)) (cp2 m)"

  have eq_assign: "obs_eq_untyped (G\<union>set locals) (G\<union>set locals\<union>{x}) (Assign x ret) (Assign x ret)"
    apply (rule self_obseq_assign)
    using globalsVret ret_locals unfolding G_def by auto
  have eq3: "eq (G\<union>set locals\<union>{x}) cp3 uf3"
    unfolding eq_def uf3_def cp3_def
    apply (rule rseq_rule_denotation)
      close (fact eq2[unfolded eq_def])
      using eq_assign unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation .
  have untouched3: "untouched (co_locals-{x}) uf3"
  proof (unfold untouched_def uf3_def, rule+, auto)
    fix m0 m y
    assume "m \<in> support_distr (uf2 m0)" and y_co: "y \<in> co_locals"
    hence m'_m0: "memory_lookup_untyped m y = memory_lookup_untyped m0 y"
      using untouched2 unfolding untouched_def by auto
    assume yx: "y\<noteq>x"
    have m_m': "memory_lookup_untyped (memory_update_untyped m x (eu_fun ret m)) y = memory_lookup_untyped m y"
      apply (rule readonly_assign[unfolded hoare_untyped_def, rule_format, where x=x and e=ret and y=y and m=m])
      using yx by auto 
    with m'_m0 show "memory_lookup_untyped (memory_update_untyped m x (eu_fun ret m)) y = memory_lookup_untyped m0 y" by simp
  qed
  
  def cp4 == "\<lambda>m. apply_to_distr (restore_locals x m) (cp3 m)"

  have eq_uf3_cp4: "eq V cp4 uf3"
  proof (unfold eq_def, rule rhoare_denotation_post_eq)
    fix m1 m2 assume m1m2: "\<forall>x\<in>V. memory_lookup_untyped m1 x = memory_lookup_untyped m2 x"
    hence m1m2': "\<And>x. x\<in>V \<Longrightarrow> memory_lookup_untyped m1 x = memory_lookup_untyped m2 x" by simp
    def m1' == "memory_lookup_untyped m1"
    def restore == "\<lambda>newmem (y::variable_untyped). 
      if x=y then newmem y else
      if vu_global y then newmem y else
      m1' y :: val"
      
    def proj1 == "\<lambda>m y. if y \<in> G\<union>set locals\<union>{x} then m y else (undefined::val)"
    def proj2 == "\<lambda>m y. if y \<in> V then m y else (undefined::val)"
    have memfuns: "(\<lambda>m y. if y \<in> V then memory_lookup_untyped m y else undefined) o (restore_locals x m1)
                   = proj2 o restore o memory_lookup_untyped"
      unfolding proj2_def restore_def o_def restore_locals_lookup m1'_def by force
    have add_proj1: "proj2 o restore = proj2 o restore o proj1"
      unfolding proj2_def proj1_def restore_def o_def 
      apply (rule ext, rule ext) using G_def by auto
    have eq_cp_uf: "apply_to_distr (proj1 o memory_lookup_untyped) (cp3 m1) = apply_to_distr (proj1 o memory_lookup_untyped) (uf3 m2)"
      using eq3 m1m2 unfolding proj1_def eq_def o_def by (rule rhoare_denotation_post_eq2)
    have rm_restore: "\<And>m. (\<forall>y\<in>(co_locals-{x})\<inter>V. m y = m1' y) \<Longrightarrow> (proj2 o restore o proj1) m = proj2 m"
      unfolding proj2_def restore_def proj1_def apply (rule ext) apply auto
      using G_def close blast
      using localsV close auto
      using G_def close blast
      by (simp add: co_locals_def')
    have supp: "\<And>m. m \<in> support_distr (uf3 m2) \<Longrightarrow> \<forall>x\<in>(co_locals-{x})\<inter>V. memory_lookup_untyped m x = memory_lookup_untyped m1 x"
      apply (rule ballI)
      apply (subst m1m2') close auto
      using untouched3 untouched_def by blast

    show "apply_to_distr (\<lambda>m y. if y\<in>V then memory_lookup_untyped m y else undefined) (cp4 m1)
        = apply_to_distr (\<lambda>m y. if y\<in>V then memory_lookup_untyped m y else undefined) (uf3 m2)"
      unfolding cp4_def
      apply (subst apply_to_distr_twice)
      apply (subst memfuns[unfolded o_def])
      apply (subst add_proj1[unfolded o_def, THEN cong, OF refl])
      apply (subst apply_to_distr_twice[symmetric, where f="\<lambda>m. proj2(restore m)"])
      apply (subst eq_cp_uf[unfolded o_def])
      apply (subst apply_to_distr_twice)
      apply (subst apply_to_distr_cong)
       apply (rule rm_restore[unfolded o_def]) using supp close (simp add: m1'_def)
      unfolding proj2_def by simp
  qed



  have uf3_unfolded: "uf3 = denotation_untyped unfolded"
    unfolding uf3_def unfolded_def uf2_def uf1_def by auto
  have cp4_callproc: "cp4 = denotation_untyped (CallProc x p args)"
    unfolding cp1_def cp2_def cp3_def cp4_def p_def
    unfolding denotation_untyped_CallProc[THEN ext]
              denotation_untyped_Assign[THEN ext]
    by auto

  show "obs_eq_untyped V V (CallProc x p args) unfolded"
    unfolding obs_eq_untyped_def rhoare_untyped_rhoare_denotation
    unfolding uf3_unfolded[symmetric] cp4_callproc[symmetric]
    using eq_uf3_cp4 unfolding eq_def by simp
qed 

(*
lemma rseq_rule1:
  assumes "\<And>m1 m2. Q m1 m2 \<Longrightarrow> Q' m1 m2"
      and "rhoare_untyped P c1 Skip Q"
      and "rhoare_untyped Q' Skip c2 R"
  shows "rhoare_untyped P c1 c2 R"
SORRY


lemma rif_rule:
  assumes "\<And>m1 m2. P m1 m2 \<Longrightarrow> eu_fun e1 m1 = eu_fun e2 m2"
      and "rhoare_untyped (\<lambda>m1 m2. P m1 m2 \<and> eu_fun e1 m1 = embedding True) then1 then2 Q"
      and "rhoare_untyped (\<lambda>m1 m2. P m1 m2 \<and> eu_fun e1 m1 \<noteq> embedding True) else1 else2 Q"
  shows "rhoare_untyped P (IfTE e1 then1 else1) (IfTE e2 then2 else2) Q"
SORRY
*)

(*
TODO: (https://www.easycrypt.info/trac/raw-attachment/wiki/BibTex/Barthe.2009.POPL.pdf)
- rand (one sided)
- while
- if
- case (+ hoare)
*)

end